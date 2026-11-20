import ConPastel.Translator.EvalM

/-!
# Applying a computation to the handle, pushed into its code

A monadic value is a function of the state's handle (`MRET`), and code that
runs one applies it: `e h`. Translated code builds such functions for every
subterm (`fn h => …` under each `bind`, in each `match` branch), so the
application `(fn h' => b) h` is mostly a redex, and `(case x of p => fn h' => b) h`
allocates a closure only to call it.

`pushH h e` is `e h` with the application pushed into the code: into a
function's body (`let h' = h in b`), the body of a `let`, both branches of an
`if` and each branch of a `case`, and applied (`e h`) everywhere else. Where a
binder would capture `h` the application stays outside. `Runs_pushH`: it runs
exactly as the application does; `EvalM_runPush`: the `EvalM_run` of it.
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL

/-- Does a clause's pattern bind `h`? -/
def clauseBinds (h : VarN) (pb : Pat × Exp) : Bool := (patBindings pb.1).contains h

mutual
/-- `e h`, pushed into `e`'s code. -/
def pushH (h : VarN) : Exp → Exp
  | .fn x b => .let_ (some x) (.var (.short h)) b
  | .let_ n e₁ e₂ =>
    if n = some h then .app .opapp [.let_ n e₁ e₂, .var (.short h)] else .let_ n e₁ (pushH h e₂)
  | .if_ c a b => .if_ c (pushH h a) (pushH h b)
  | .mat e pes =>
    if pes.any (clauseBinds h) then .app .opapp [.mat e pes, .var (.short h)]
    else .mat e (pushHs h pes)
  | e => .app .opapp [e, .var (.short h)]

/-- `pushH` in each clause body. -/
def pushHs (h : VarN) : List (Pat × Exp) → List (Pat × Exp)
  | [] => []
  | (p, b) :: r => (p, pushH h b) :: pushHs h r
end

theorem pushHs_fst (h : VarN) : ∀ pes : List (Pat × Exp), (pushHs h pes).map Prod.fst = pes.map Prod.fst
  | [] => rfl
  | (p, b) :: r => by simp [pushHs, pushHs_fst h r]

/-! ## Pattern matching binds only the pattern's variables -/

mutual
theorem pmatch_binds {envC : Namespace ModN ConN (Nat × Stamp)} {store : Store Value} :
    ∀ (p : Pat) (v : Value) (acc env' : List (VarN × Value)),
    pmatch envC store p v acc = .match env' →
    ∃ l, env' = l ++ acc ∧ ∀ x ∈ l.map Prod.fst, x ∈ patBindings p
  | .pany, v, acc, env', h => by
    simp only [pmatch] at h; cases h; exact ⟨[], by simp, by simp⟩
  | .pvar n, v, acc, env', h => by
    simp only [pmatch] at h; cases h; exact ⟨[(n, v)], by simp, by simp [patBindings]⟩
  | .plit l, v, acc, env', h => by
    unfold pmatch at h
    repeat' (first | contradiction | (split at h))
    all_goals first | contradiction | (cases h; exact ⟨[], by simp, by simp⟩)
  | .pcon c ps, v, acc, env', h => by
    rcases v with _ | ⟨_ | _, _⟩ | _ | _ | _ | _ | _ <;> cases c <;> (try simp only [pmatch] at h)
    all_goals repeat' (first | contradiction | (split at h))
    all_goals first
      | contradiction
      | (obtain ⟨l, rfl, hl⟩ := pmatchList_binds ps _ acc env' h
         exact ⟨l, rfl, by simpa [patBindings] using hl⟩)
  | .pref p, v, acc, env', h => by
    cases v <;> (try simp only [pmatch] at h)
    all_goals repeat' (first | contradiction | (split at h))
    all_goals first
      | contradiction
      | (obtain ⟨l, rfl, hl⟩ := pmatch_binds p _ acc env' h
         exact ⟨l, rfl, by simpa [patBindings] using hl⟩)
  | .pas p n, v, acc, env', h => by
    simp only [pmatch] at h
    obtain ⟨l, rfl, hl⟩ := pmatch_binds p v _ env' h
    refine ⟨l ++ [(n, v)], by simp, ?_⟩
    intro x hx
    simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    simp only [patBindings, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with hx | hx
    · exact Or.inl (hl x hx)
    · exact Or.inr hx
  | .ptannot p t, v, acc, env', h => by
    simp only [pmatch] at h
    obtain ⟨l, rfl, hl⟩ := pmatch_binds p v acc env' h
    exact ⟨l, rfl, by simpa [patBindings] using hl⟩

theorem pmatchList_binds {envC : Namespace ModN ConN (Nat × Stamp)} {store : Store Value} :
    ∀ (ps : List Pat) (vs : List Value) (acc env' : List (VarN × Value)),
    pmatchList envC store ps vs acc = .match env' →
    ∃ l, env' = l ++ acc ∧ ∀ x ∈ l.map Prod.fst, x ∈ patsBindings ps
  | [], [], acc, env', h => by
    simp only [pmatchList] at h; cases h; exact ⟨[], by simp, by simp⟩
  | [], _ :: _, acc, env', h => by simp only [pmatchList] at h; exact nomatch h
  | _ :: _, [], acc, env', h => by simp only [pmatchList] at h; exact nomatch h
  | p :: ps, v :: vs, acc, env', h => by
    simp only [pmatchList] at h
    split at h
    · split at h <;> exact nomatch h
    · exact nomatch h
    · rename_i env₁ h₁
      obtain ⟨l₁, rfl, hl₁⟩ := pmatch_binds p v acc env₁ h₁
      obtain ⟨l₂, rfl, hl₂⟩ := pmatchList_binds ps vs _ env' h
      refine ⟨l₂ ++ l₁, by simp, ?_⟩
      intro x hx
      simp only [List.map_append, List.mem_append] at hx
      simp only [patsBindings, List.mem_append]
      rcases hx with hx | hx
      · exact Or.inl (hl₂ x hx)
      · exact Or.inr (hl₁ x hx)
end

theorem lookup_none_of_not_mem {h : VarN} : ∀ (l : List (VarN × Value)), h ∉ l.map Prod.fst →
    l.lookup h = none
  | [], _ => rfl
  | (k, v) :: r, hn => by
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    have : (h == k) = false := beq_eq_false_iff_ne.mpr hn.1
    simp [List.lookup, this, lookup_none_of_not_mem r hn.2]

/-- A clause whose pattern does not bind `h` keeps `h`'s binding. -/
theorem nsLookup_clause {envC : Namespace ModN ConN (Nat × Stamp)} {store : Store Value}
    {p : Pat} {v : Value} {bs : List (VarN × Value)} {ev : Namespace ModN VarN Value} {h : VarN}
    {w : Value} (hm : pmatch envC store p v [] = .match bs) (hnb : h ∉ patBindings p)
    (hh : nsLookup ev (.short h) = some w) :
    nsLookup (nsAppend (alistToNs bs) ev) (.short h) = some w := by
  obtain ⟨l, rfl, hl⟩ := pmatch_binds p v [] bs hm
  rw [nsLookup_nsAppend_alist_short]
  have hn : h ∉ (l ++ []).map Prod.fst := fun hx => hnb (hl h (by simpa using hx))
  have : (l ++ []).lookup h = none := lookup_none_of_not_mem _ hn
  rw [this]; exact hh

/-! ## The control steps, at any result -/

theorem evaluate_let_vals {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {n : Option VarN}
    {e₁ e₂ : Exp} {vs : List Value} (h₁ : evaluate s env [e₁] = (s₁, .val vs)) :
    evaluate s env [.let_ n e₁ e₂] = evaluate s₁ { env with v := nsOptBind n (headValue vs) env.v } [e₂] := by
  have hfix : fixClock s (s₁, (Result.val vs : Result (List Value) Value)) = (s₁, .val vs) := by
    rw [← h₁]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp [h₁, hfix]

theorem evaluate_if_vals {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {c e₂ e₃ e : Exp}
    {vs : List Value} (h₁ : evaluate s env [c] = (s₁, .val vs)) (hd : doIf (headValue vs) e₂ e₃ = some e) :
    evaluate s env [.if_ c e₂ e₃] = evaluate s₁ env [e] := by
  have hfix : fixClock s (s₁, (Result.val vs : Result (List Value) Value)) = (s₁, .val vs) := by
    rw [← h₁]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp only [h₁, hfix]
  split
  · next h => rw [hd] at h; exact nomatch h
  · next e' h => rw [hd] at h; cases h; rfl

theorem evaluate_mat_vals {σ : Type} {s s₁ : State σ} {env : SemEnv Value} {e : Exp}
    {pes : List (Pat × Exp)} {vs : List Value} (h₁ : evaluate s env [e] = (s₁, .val vs))
    (hc : canPmatchAll env.c s₁.refs (pes.map Prod.fst) (headValue vs) = true) :
    evaluate s env [.mat e pes] = evaluateMatch s₁ env (headValue vs) pes bindExnV := by
  have hfix : fixClock s (s₁, (Result.val vs : Result (List Value) Value)) = (s₁, .val vs) := by
    rw [← h₁]; exact fixClock_evaluate s env _
  rw [evaluate]
  simp [h₁, hfix, hc]

/-- A run that reaches a value. -/
theorem state_clock_eq {σ : Type} {s s' : State σ} {a b : Nat}
    (h : { s with clock := a } = { s' with clock := b }) (k : Nat) :
    { s with clock := k } = { s' with clock := k } := by
  cases s; cases s'; simp only [State.mk.injEq] at h ⊢; simp_all

/-! ## The push -/

/-- The clause selection of a `case` that returns: the chosen clause, and the
pushed clauses select the same one (at any clock: matching reads only the store). -/
theorem evaluateMatch_pushHs {σ : Type} {h : VarN} {env : SemEnv Value} {w err : Value} :
    ∀ (pes : List (Pat × Exp)) {t X : State σ} {r : Result (List Value) Value},
    pes.any (clauseBinds h) = false →
    evaluateMatch t env w pes err = (X, r) → r ≠ .err (.raise err) → (∀ e, r ≠ .err (.abort e)) →
    ∃ p b bs, (p, b) ∈ pes ∧ h ∉ patBindings p ∧ pmatch env.c t.refs p w [] = .match bs ∧
      evaluate t { env with v := nsAppend (alistToNs bs) env.v } [b] = (X, r) ∧
      ∀ (t' : State σ), t'.refs = t.refs →
        evaluateMatch t' env w (pushHs h pes) err =
          evaluate t' { env with v := nsAppend (alistToNs bs) env.v } [pushH h b]
  | [], t, X, r, _, hm, hr, _ => by
    simp only [evaluateMatch] at hm; cases hm; exact absurd rfl hr
  | (p, b) :: rest, t, X, r, hany, hm, hr, hab => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hany
    have hnb : h ∉ patBindings p := by
      intro hx; have := hany.1; simp [clauseBinds, hx] at this
    rw [evaluateMatch] at hm
    split at hm
    · rename_i hnd
      split at hm
      · rename_i hno
        obtain ⟨p', b', bs, hmem, hnb', hpm, hev, hpush⟩ := evaluateMatch_pushHs rest hany.2 hm hr hab
        refine ⟨p', b', bs, List.mem_cons_of_mem _ hmem, hnb', hpm, hev, fun t' ht' => ?_⟩
        rw [pushHs, evaluateMatch]
        simp only [hnd, ite_true, ht', hno]
        exact hpush t' ht'
      · cases hm; exact absurd rfl (hab _)
      · rename_i bs hbs
        refine ⟨p, b, bs, List.mem_cons_self .., hnb, hbs, hm, fun t' ht' => ?_⟩
        rw [pushHs, evaluateMatch]
        simp only [hnd, ite_true, ht', hbs]
    · cases hm; exact absurd rfl (hab _)

/-- The fallback: the application itself. -/
theorem Runs_app_h {τ : Type} {h : VarN} {hv : Value} (e : Exp) {env : SemEnv Value}
    {s s₁ s₂ : State τ} {vf : Value} {env' : SemEnv Value} {body : Exp} {r : Result (List Value) Value}
    (hh : nsLookup env.v (.short h) = some hv)
    (he : Runs s env [e] s₁ (.val [vf])) (happ : doOpApp [vf, hv] = some (env', body))
    (hb : Runs s₁ env' [body] s₂ r) (hr : r ≠ .err (.abort .timeoutError)) :
    Runs s env [.app .opapp [e, .var (.short h)]] s₂ r := by
  refine Runs.app_opapp_any ?_ happ hb hr
  obtain ⟨c₁, c₂, hc⟩ := he
  refine ⟨c₁, c₂, ?_⟩
  have ha' : evaluate { s with clock := c₁ } env [.var (.short h)] = ({ s with clock := c₁ }, .val [hv]) := by
    simp [evaluate, hh]
  exact evaluate_cons_val ha' hc

/-- **The push runs as the application does.** -/
theorem Runs_pushH {τ : Type} {h : VarN} {hv : Value} (e : Exp) {env : SemEnv Value}
    {s s₁ s₂ : State τ} {vf : Value} {env' : SemEnv Value} {body : Exp} {r : Result (List Value) Value}
    (hh : nsLookup env.v (.short h) = some hv)
    (he : Runs s env [e] s₁ (.val [vf])) (happ : doOpApp [vf, hv] = some (env', body))
    (hb : Runs s₁ env' [body] s₂ r) (hr : r ≠ .err (.abort .timeoutError)) :
    Runs s env [pushH h e] s₂ r := by
  match e with
  | .fn x b =>
    obtain ⟨c₁, c₂, hc⟩ := he
    simp only [evaluate, Prod.mk.injEq] at hc
    obtain ⟨hs, hv'⟩ := hc
    simp only [Result.val.injEq, List.cons.injEq, and_true] at hv'
    subst hv'
    simp only [doOpApp, Option.some.injEq, Prod.mk.injEq] at happ
    obtain ⟨rfl, rfl⟩ := happ
    obtain ⟨b₁, b₂, hbr⟩ := hb
    refine ⟨b₁, b₂, ?_⟩
    rw [pushH, state_clock_eq hs b₁]
    rw [evaluate_let_vals (s₁ := { s₁ with clock := b₁ }) (vs := [hv]) (by simp [evaluate, hh])]
    simpa [nsOptBind, headValue, Flapjack.holHd] using hbr
  | .let_ n e₁ e₂ =>
    rw [pushH]
    split
    · exact Runs_app_h _ hh he happ hb hr
    · rename_i hn
      obtain ⟨c₁, c₂, hc⟩ := he
      rw [evaluate] at hc
      simp only [fixClock_evaluate] at hc
      generalize hr₁ : evaluate { s with clock := c₁ } env [e₁] = p₁ at hc
      obtain ⟨t, r₁⟩ := p₁
      cases r₁ with
      | err x => simp at hc
      | val vs =>
        simp only at hc
        have hh' : nsLookup (nsOptBind n (headValue vs) env.v) (.short h) = some hv := by
          cases n with
          | none => simpa [nsOptBind] using hh
          | some x => exact nsLookup_optBind_ne (fun he => hn (by rw [he])) hh
        have h₂ : Runs t { env with v := nsOptBind n (headValue vs) env.v } [e₂] s₁ (.val [vf]) :=
          ⟨t.clock, c₂, by simpa using hc⟩
        obtain ⟨d₁, d₂, hd⟩ := Runs_pushH e₂ hh' h₂ happ hb hr
        refine ⟨d₁ + c₁, t.clock + d₂, ?_⟩
        have hr₁' := Runs.add_clock (s' := t) (ck₂ := t.clock) (by simpa using hr₁) (by simp) d₁
        rw [evaluate_let_vals hr₁']
        have := Runs.add_clock hd hr t.clock
        rw [Nat.add_comm d₁ t.clock]
        simpa using this
  | .if_ c a b =>
    rw [pushH]
    obtain ⟨c₁, c₂, hc⟩ := he
    rw [evaluate] at hc
    simp only [fixClock_evaluate] at hc
    generalize hr₁ : evaluate { s with clock := c₁ } env [c] = p₁ at hc
    obtain ⟨t, r₁⟩ := p₁
    cases r₁ with
    | err x => simp at hc
    | val vs =>
      simp only at hc
      split at hc
      · simp [typeError] at hc
      · rename_i e' hd
        obtain ⟨bb, hbv, rfl⟩ := doIf_success_boolean _ _ _ _ hd
        have h₂ : Runs t env [if bb then a else b] s₁ (.val [vf]) := ⟨t.clock, c₂, by simpa using hc⟩
        have hpush : Runs t env [pushH h (if bb then a else b)] s₂ r := by
          cases bb
          · exact Runs_pushH b hh h₂ happ hb hr
          · exact Runs_pushH a hh h₂ happ hb hr
        obtain ⟨d₁, d₂, hd'⟩ := hpush
        refine ⟨d₁ + c₁, t.clock + d₂, ?_⟩
        have hr₁' := Runs.add_clock (s' := t) (ck₂ := t.clock) (by simpa using hr₁) (by simp) d₁
        have hdo : doIf (headValue vs) (pushH h a) (pushH h b) = some (pushH h (if bb then a else b)) := by
          rw [hbv, doIf_boolValue]; cases bb <;> rfl
        rw [evaluate_if_vals hr₁' hdo]
        have := Runs.add_clock hd' hr t.clock
        rw [Nat.add_comm d₁ t.clock]
        simpa using this
  | .mat e pes =>
    rw [pushH]
    split
    · exact Runs_app_h _ hh he happ hb hr
    · rename_i hany
      simp only [Bool.not_eq_true] at hany
      obtain ⟨c₁, c₂, hc⟩ := he
      rw [evaluate] at hc
      simp only [fixClock_evaluate] at hc
      generalize hr₁ : evaluate { s with clock := c₁ } env [e] = p₁ at hc
      obtain ⟨t, r₁⟩ := p₁
      cases r₁ with
      | err x => simp at hc
      | val vs =>
        simp only at hc
        split at hc
        · rename_i hcan
          obtain ⟨p, b, bs, hmem, hnb, hpm, hev, hpush⟩ :=
            evaluateMatch_pushHs pes hany hc (by simp) (by simp)
          have hh' : nsLookup (nsAppend (alistToNs bs) env.v) (.short h) = some hv :=
            nsLookup_clause hpm hnb hh
          have h₂ : Runs t { env with v := nsAppend (alistToNs bs) env.v } [b] s₁ (.val [vf]) :=
            ⟨t.clock, c₂, by simpa using hev⟩
          have := List.sizeOf_lt_of_mem hmem
          obtain ⟨d₁, d₂, hd'⟩ := Runs_pushH b hh' h₂ happ hb hr
          refine ⟨d₁ + c₁, t.clock + d₂, ?_⟩
          have hr₁' := Runs.add_clock (s' := t) (ck₂ := t.clock) (by simpa using hr₁) (by simp) d₁
          have hcan' : canPmatchAll env.c { t with clock := d₁ + t.clock }.refs
              ((pushHs h pes).map Prod.fst) (headValue vs) = true := by
            rw [pushHs_fst]; simpa using hcan
          rw [evaluate_mat_vals hr₁' hcan', hpush { t with clock := d₁ + t.clock } rfl]
          have := Runs.add_clock hd' hr t.clock
          rw [Nat.add_comm d₁ t.clock]
          simpa using this
        · simp [typeError] at hc
  | .raise _ | .handle _ _ | .lit _ | .con _ _ | .var _ | .app _ _ | .log _ _ _ | .letrec _ _
  | .tannot _ _ | .lannot _ _ =>
    simp only [pushH]
    exact Runs_app_h _ hh he happ hb hr
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals (simp at this; omega)

/-- `EvalM_run`, with the application pushed into the code. -/
theorem EvalM_runPush {σ ε β : Type} {RF : Nat → StateRel σ} {A : RefInv β} {B : RefInv ε}
    {env : SemEnv Value} {ef : Exp} {h : VarN} {b : Bool} {loc : Nat}
    {m : StateT σ (Except ε) β} (hh : nsLookup env.v (.short h) = some (.loc b loc))
    (hf : Eval env ef (MRET RF A B m)) :
    EvalM (RF loc) env (pushH h ef) A B m := by
  intro τ s st hst
  obtain ⟨vf, extra, hfr, hM⟩ := hf τ s
  have hst₁ := StateRel.rel_append hst extra
  obtain ⟨env', body, happ, refs', res, hrun, hfm, hm⟩ := hM τ { s with refs := s.refs ++ extra } st b loc hst₁
  refine ⟨refs', res, Runs_pushH ef hh hfr.runs happ (by simpa using hrun) hm.not_timeout,
    (Frame.append hst extra).trans hfm, hm⟩

end ConPastel.Translator
