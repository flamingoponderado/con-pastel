import ConPastel.Translator.Table
import ConPastel.Translator.List
import ConPastel.Translator.Recursion

/-!
# Reading a table's buckets natively

Growing a table (`expandM`) reads every bucket before reinserting the entries.
Written with `tGetB`, that read was a translated monadic loop, a closure call and
a fresh cell read per bucket, and it was the checker's largest single cost (the
kernel's memo tables are reset at every environment change and regrow). Here
`tReadAll` is a primitive: a local recursive CakeML function over the bucket
array (`raCode`), proved to return the buckets as a list (`EvalM_tReadAll`).
-/

namespace ConPastel.Translator
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL
open Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

section
variable {K V ε : Type}
/-- All the buckets, in order (the state unchanged). -/
def tReadAll : StateT (TRaw K V) (Except ε) (List (Bkt K V)) := fun st => .ok (st.buckets.toList, st)
end

def raAr : VarN := ofString "ar"
def raGo : VarN := ofString "go"
def raJ : VarN := ofString "j"

/-- `go j = if j < length ar then ar[j] :: go (j + 1) else []`. -/
def raBody : Exp :=
  .if_ (ltLen (.short raJ) (.short raAr))
    (.con (some (.short consC)) [.app .asub [.var (.short raAr), .var (.short raJ)],
      .app .opapp [.var (.short raGo), .app (.arith .add .intT) [.var (.short raJ), .lit (.intLit 1)]]])
    (.con (some (.short nilC)) [])

def raFuns : List (VarN × VarN × Exp) := [(raGo, raJ, raBody)]

/-- `let ar = Array.sub h 0 in letrec go … in go 0`. -/
def raCode (h : VarN) : Exp :=
  .let_ (some raAr) (cellArr h) (.letrec raFuns (.app .opapp [.var (.short raGo), .lit (.intLit 0)]))

theorem ra_nodup : (raFuns.map fun (f, _, _) => f).Nodup := by simp [raFuns]
theorem ra_find : findRecFun raGo raFuns = some (raJ, raBody) := by
  simp [raFuns, findRecFun]

/-- A two-argument constructor, once its arguments have run (right to left). -/
theorem Runs.con2 {τ : Type} {s s₁ : State τ} {env : SemEnv Value} {c : ConN} {stamp : Stamp}
    {e₁ e₂ : Exp} {v₁ v₂ : Value} (hl : nsLookup env.c (.short c) = some (2, stamp))
    (h : Runs s env [e₂, e₁] s₁ (.val [v₂, v₁])) :
    Runs s env [.con (some (.short c)) [e₁, e₂]] s₁ (.val [.conv (some stamp) [v₁, v₂]]) := by
  obtain ⟨a₁, a₂, ha⟩ := h
  refine ⟨a₁, a₂, ?_⟩
  rw [evaluate]
  simp [doConCheck, hl, ha, buildConv]

theorem Eval.runs_at {τ : Type} {env : SemEnv Value} {e : Exp} {P : Value → Prop} (h : Eval env e P)
    (s : State τ) : ∃ v extra, Runs s env [e] { s with refs := s.refs ++ extra } (.val [v]) ∧ P v := by
  obtain ⟨v, r, hr, hp⟩ := h τ s
  exact ⟨v, r, hr.runs, hp⟩

theorem ra_ar_j : raAr ≠ raJ := by decide
theorem ra_ar_go : raAr ≠ raGo := by decide
theorem ra_go_j : raGo ≠ raJ := by decide

theorem ra_lookup_ar {envL : SemEnv Value} {x : Value} :
    nsLookup (recBodyEnv envL raFuns raJ x).v (.short raAr) = nsLookup envL.v (.short raAr) := by
  simp [recBodyEnv, raFuns, buildRecEnv, nsLookup_nsBind_short, ra_ar_j, ra_ar_go]

theorem ra_lookup_go {envL : SemEnv Value} {x : Value} :
    nsLookup (recBodyEnv envL raFuns raJ x).v (.short raGo) = some (.recclosure envL raFuns raGo) := by
  simp [recBodyEnv, raFuns, buildRecEnv, nsLookup_nsBind_short, ra_go_j]

theorem ra_lookup_j {envL : SemEnv Value} {x : Value} :
    nsLookup (recBodyEnv envL raFuns raJ x).v (.short raJ) = some x := by
  simp [recBodyEnv, nsLookup_nsBind_short]

theorem ra_app (envL : SemEnv Value) (x : Value) :
    doOpApp [.recclosure envL raFuns raGo, x] = some (recBodyEnv envL raFuns raJ x, raBody) := by
  simp [doOpApp, ra_nodup, ra_find]; rfl

/-- The loop: from `j`, the remaining buckets as a list. -/
theorem ra_loop {K V τ : Type} {BI : RefInv (Bkt K V)} {envL : SemEnv Value} {b : Bool} {a : Nat}
    {bs : List Value} {xs : List (Bkt K V)}
    (hc : HasListCons envL.c) (har : nsLookup envL.v (.short raAr) = some (.loc b a))
    (hF : List.Forall₂ BI xs bs) :
    ∀ (k j : Nat), j + k = bs.length → ∀ (s : State τ), s.refs[a]? = some (.varray bs) →
      ∃ v extra, Runs s (recBodyEnv envL raFuns raJ (.litv (.intLit j))) [raBody]
        { s with refs := s.refs ++ extra } (.val [v]) ∧ LIST BI (xs.drop j) v := by
  have hlen := forall₂_length hF
  intro k
  induction k with
  | zero =>
    intro j hj s hs
    have hlt : ¬ j < bs.length := by omega
    have hcond := evaluate_ltLen { s with clock := s.clock } (env := recBodyEnv envL raFuns raJ (.litv (.intLit j)))
      (arr := .short raAr) (ix := .short raJ) (by rw [ra_lookup_ar]; exact har) ra_lookup_j hs
    obtain ⟨v, extra, hr, hv⟩ := (Eval_nil (A := BI) (env := recBodyEnv envL raFuns raJ (.litv (.intLit j)))
      (by simpa [recBodyEnv] using hc)).runs_at s
    refine ⟨v, extra, ?_, ?_⟩
    · refine Runs.if_ (b := false) ⟨s.clock, s.clock, ?_⟩ (by simpa using hr) (by simp)
      unfold ltLen; simpa [decide_eq_false hlt] using hcond
    · rw [List.drop_eq_nil_of_le (by omega)]; exact hv
  | succ k ih =>
    intro j hj s hs
    have hlt : j < bs.length := by omega
    have hcond := evaluate_ltLen { s with clock := s.clock } (env := recBodyEnv envL raFuns raJ (.litv (.intLit j)))
      (arr := .short raAr) (ix := .short raJ) (by rw [ra_lookup_ar]; exact har) ra_lookup_j hs
    -- the recursive call, first (arguments right to left)
    have hadd : Eval (recBodyEnv envL raFuns raJ (.litv (.intLit j)))
        (.app (.arith .add .intT) [.var (.short raJ), .lit (.intLit 1)]) (NAT (j + 1)) :=
      Eval_nat_add (Eval_var _ _ _ _ ra_lookup_j rfl) (Eval_lit _ _ _ rfl)
    obtain ⟨vj, ex₁, hj₁, hvj⟩ := hadd.runs_at s
    have hvj' : vj = .litv (.intLit (j + 1)) := by simpa [NAT] using hvj
    subst hvj'
    have hs₁ : ({ s with refs := s.refs ++ ex₁ } : State τ).refs[a]? = some (.varray bs) := by
      have := (List.getElem?_eq_some_iff.mp hs).1
      simp [List.getElem?_append_left this, hs]
    obtain ⟨vr, ex₂, hr₂, hvr⟩ := ih (j + 1) (by omega) _ hs₁
    have hgo : Runs { s with refs := s.refs ++ ex₁ } (recBodyEnv envL raFuns raJ (.litv (.intLit j)))
        [.var (.short raGo)] { s with refs := s.refs ++ ex₁ } (.val [.recclosure envL raFuns raGo]) :=
      ⟨0, 0, by simp [evaluate, ra_lookup_go]⟩
    have hcall : Runs s (recBodyEnv envL raFuns raJ (.litv (.intLit j)))
        [.app .opapp [.var (.short raGo), .app (.arith .add .intT) [.var (.short raJ), .lit (.intLit 1)]]]
        { s with refs := s.refs ++ ex₁ ++ ex₂ } (.val [vr]) :=
      Runs.app_opapp (Runs.cons hj₁ hgo) (ra_app envL _) (by simpa using hr₂)
    have hs₂ : ({ s with refs := s.refs ++ ex₁ ++ ex₂ } : State τ).refs[a]? = some (.varray bs) := by
      have := (List.getElem?_eq_some_iff.mp hs).1
      simp [List.append_assoc, List.getElem?_append_left this, hs]
    have hsub := Runs.asub (s := { s with refs := s.refs ++ ex₁ ++ ex₂ })
      (env := recBodyEnv envL raFuns raJ (.litv (.intLit j)))
      (by rw [ra_lookup_ar]; exact har) ra_lookup_j hs₂ hlt
    have hcons := Runs.con2 (c := consC) (stamp := .typeStamp consC 1)
      (by simpa [recBodyEnv] using hc.cons) (Runs.cons hcall hsub)
    refine ⟨.conv (some (.typeStamp consC 1)) [bs[j], vr], ex₁ ++ ex₂, ?_, ?_⟩
    · refine Runs.if_ (b := true) ⟨s.clock, s.clock, ?_⟩ (by simpa [List.append_assoc] using hcons) (by simp)
      unfold ltLen; simpa [decide_eq_true hlt] using hcond
    · have hxj : j < xs.length := by omega
      rw [List.drop_eq_getElem_cons hxj]
      exact ⟨_, _, forall₂_get hF j hxj, hvr, rfl⟩

theorem Runs.letrec_ {τ : Type} {s s' : State τ} {env : SemEnv Value} {funs : List (VarN × VarN × Exp)}
    {e : Exp} {r : Result (List Value) Value} (hnd : (funs.map fun (n, _, _) => n).Nodup)
    (h : Runs s { env with v := buildRecEnv funs env env.v } [e] s' r) :
    Runs s env [.letrec funs e] s' r := by
  obtain ⟨a₁, a₂, ha⟩ := h
  exact ⟨a₁, a₂, by rw [evaluate]; simpa [hnd] using ha⟩

/-- `tReadAll`: the bucket array read into a list by a native loop. -/
theorem EvalM_tReadAll {K V ε : Type} {BI : RefInv (Bkt K V)} {B : RefInv ε} {env : SemEnv Value}
    {h : VarN} {b : Bool} {tl : Nat}
    (hh : nsLookup env.v (.short h) = some (.loc b tl)) (hc : HasListCons env.c) :
    EvalM (tblRel BI tl) env (raCode h) (LIST BI) B (tReadAll (K := K) (V := V)) := by
  intro τ s st hst
  obtain ⟨b', a, bs, ht⟩ := tblRel_at hst
  have hcell := evaluate_asub_lit { s with clock := s.clock } hh ht.cell (k := 0) (by simp)
  simp only [List.getElem_cons_zero] at hcell
  let env₁ : SemEnv Value := { env with v := nsOptBind (some raAr) (.loc b' a) env.v }
  have har : nsLookup env₁.v (.short raAr) = some (.loc b' a) := nsl_self
  have hlen := forall₂_length ht.elems
  obtain ⟨v, extra, hr, hv⟩ := ra_loop (τ := τ) (envL := env₁) (by simpa [env₁] using hc) har ht.elems
    bs.length 0 (by omega) s ht.arr
  have hcall : Runs s { env₁ with v := buildRecEnv raFuns env₁ env₁.v }
      [.app .opapp [.var (.short raGo), .lit (.intLit 0)]] { s with refs := s.refs ++ extra } (.val [v]) := by
    refine Runs.app_opapp (vf := .recclosure env₁ raFuns raGo) (vx := .litv (.intLit 0))
      ⟨s.clock, s.clock, ?_⟩ (ra_app env₁ _) (by simpa using hr)
    exact evaluate_cons_val (s₁ := { s with clock := s.clock }) (by simp [evaluate]) (by simp [evaluate, nsLookup_buildRecEnv, raFuns])
  refine ⟨s.refs ++ extra, .val [v], ?_, Frame.append hst _, StateRel.rel_append hst _, v, rfl, ?_⟩
  · exact Runs.let_ ⟨s.clock, s.clock, hcell⟩ (Runs.letrec_ ra_nodup hcall) (by simp)
  · simpa [tReadAll] using hv

end ConPastel.Translator
