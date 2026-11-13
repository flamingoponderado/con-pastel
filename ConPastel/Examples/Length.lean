import ConPastel.Translator.List

/-!
# Milestone 2 check: `List.length`, polymorphic, by hand
-/

namespace ConPastel.Examples
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open Flapjack.Basis.Pure.MlString ConPastel.Translator

def v (s : String) : Exp := .var (.short (ofString s))

def lengthBody : Exp :=
  .mat (v "l") (conClauses
    [(nilC, [], .lit (.intLit 0)),
     (consC, [ofString "x", ofString "xs"],
      .app (.arith .add .intT) [.lit (.intLit 1), .app .opapp [v "len", v "xs"]])])

def lengthFuns : List (VarN × VarN × Exp) := [(ofString "len", ofString "l", lengthBody)]

theorem length_cert {α : Type} (a : RefInv α) (envC : SemEnv Value) (hc : HasListCons envC.c) :
    Arrow (LIST a) NAT List.length (.recclosure envC lengthFuns (ofString "len")) := by
  intro l
  induction l with
  | nil =>
    intro lv hl
    apply AppReturns_recclosure (x := ofString "l") (body := lengthBody) (by decide)
      (by simp [findRecFun, lengthFuns])
    unfold lengthBody
    refine Eval_mat (listCases_flat hc _ _ _ _ (by decide))
      (Eval_var _ _ lv _ (by simp [recBodyEnv, nsLookup_nsBind_short]) hl) ?_
    intro w hw
    exact ⟨nilC, [], _, [], by simp, hw, rfl, Eval_lit _ _ _ rfl⟩
  | cons x xs ih =>
    intro lv hl
    obtain ⟨xv, xsv, hx, hxs, rfl⟩ := hl
    apply AppReturns_recclosure (x := ofString "l") (body := lengthBody) (by decide)
      (by simp [findRecFun, lengthFuns])
    unfold lengthBody
    refine Eval_mat (listCases_flat hc _ _ _ _ (by decide))
      (Eval_var _ _ _ (· = _) (by simp [recBodyEnv, nsLookup_nsBind_short]; rfl) rfl) ?_
    rintro w rfl
    refine ⟨consC, [ofString "x", ofString "xs"],
      .app (.arith .add .intT) [.lit (.intLit 1), .app .opapp [v "len", v "xs"]], [xv, xsv],
      by simp, rfl, rfl, ?_⟩
    have hne₃ : ofString "len" ≠ ofString "l" := by decide
    let env₀ := clauseEnv (recBodyEnv envC lengthFuns (ofString "l")
      (.conv (some (.typeStamp consC 1)) [xv, xsv])) [ofString "x", ofString "xs"] [xv, xsv]
    have lk_xs : nsLookup env₀.v (.short (ofString "xs")) = some xsv := by
      simp [env₀, clauseEnv, nsLookup_nsAppend_alist_short, List.lookup]
    have lk_len : nsLookup env₀.v (.short (ofString "len")) =
        some (.recclosure envC lengthFuns (ofString "len")) := by
      simp only [env₀, clauseEnv, nsLookup_nsAppend_alist_short, recBodyEnv, nsLookup_nsBind_short]
      simp [List.lookup, hne₃]
      exact nsLookup_buildRecEnv (by decide)
    have hrec := Eval_app (Q := NAT xs.length)
      (Eval_var env₀ _ _ (· = .recclosure envC lengthFuns (ofString "len")) lk_len rfl)
      (Eval_var env₀ _ xsv _ lk_xs hxs) (fun fv yv hf hy => by subst hf; exact ih yv hy)
    exact Eval_weaken (Eval_int_add (Eval_lit _ _ (INT 1) rfl) hrec) fun w hw => by
      simp only [INT, NAT] at hw ⊢; rw [hw]; simp; omega

end ConPastel.Examples
