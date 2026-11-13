import ConPastel.Program.Decls

/-!
# Deciding the constructor-arity side condition

`Dlet`/`Dletrec` require `everyExp (oneConCheck env.c) e`. `conOk tbl e`
checks the same against an arity table, by structural recursion, so the
kernel can decide it on concrete programs.
-/

namespace ConPastel.Program
open Flapjack Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.NamespaceHOL
open private everyExpList everyExpClauses everyExpFuns from Flapjack.AstHOL.Syntax

def conHeadOk (tbl : List (ConN × Nat)) : Option (Ident ModN ConN) → Nat → Bool
  | none, _ => true
  | some (.short c), n => tbl.lookup c == some n
  | some (.long _ _), _ => false

mutual
def conOk (tbl : List (ConN × Nat)) : Exp → Bool
  | .raise e | .fn _ e | .tannot e _ | .lannot e _ => conOk tbl e
  | .handle e cs | .mat e cs => conOk tbl e && conOkClauses tbl cs
  | .con n es => conHeadOk tbl n es.length && conOkList tbl es
  | .app _ es => conOkList tbl es
  | .log _ a b | .let_ _ a b => conOk tbl a && conOk tbl b
  | .if_ a b c => conOk tbl a && conOk tbl b && conOk tbl c
  | .letrec fs b => conOk tbl b && conOkFuns tbl fs
  | .lit _ | .var _ => true
def conOkList (tbl : List (ConN × Nat)) : List Exp → Bool
  | [] => true
  | e :: es => conOk tbl e && conOkList tbl es
def conOkClauses (tbl : List (ConN × Nat)) : List (Pat × Exp) → Bool
  | [] => true
  | (_, e) :: cs => conOk tbl e && conOkClauses tbl cs
def conOkFuns (tbl : List (ConN × Nat)) : List (VarN × VarN × Exp) → Bool
  | [] => true
  | (_, _, e) :: fs => conOk tbl e && conOkFuns tbl fs
end

/-- The table agrees with the constructor environment on arities. -/
def TableOk (tbl : List (ConN × Nat)) (envC : Namespace ModN ConN (Nat × Stamp)) : Prop :=
  ∀ c n, tbl.lookup c = some n → ∃ st, nsLookup envC (.short c) = some (n, st)

theorem conHeadOk_doConCheck {tbl : List (ConN × Nat)} {envC : Namespace ModN ConN (Nat × Stamp)}
    (ht : TableOk tbl envC) (n : Option (Ident ModN ConN)) (k : Nat) (h : conHeadOk tbl n k = true) :
    doConCheck envC n k = true := by
  match n with
  | none => rfl
  | some (.short c) =>
    simp only [conHeadOk, beq_iff_eq] at h
    obtain ⟨st, hst⟩ := ht c k h
    simp [doConCheck, hst]
  | some (.long _ _) => simp [conHeadOk] at h

theorem oneConCheck_of {tbl : List (ConN × Nat)} {envC : Namespace ModN ConN (Nat × Stamp)}
    (ht : TableOk tbl envC) (n : Option (Ident ModN ConN)) (es : List Exp)
    (h : conHeadOk tbl n es.length = true) : oneConCheck envC (.con n es) = true := by
  simp [oneConCheck, conHeadOk_doConCheck ht n es.length h]

mutual
theorem everyExp_of_conOk {tbl : List (ConN × Nat)} {envC : Namespace ModN ConN (Nat × Stamp)}
    (ht : TableOk tbl envC) : ∀ e, conOk tbl e = true → everyExp (oneConCheck envC) e = true
  | .raise e, h | .fn _ e, h | .tannot e _, h | .lannot e _, h => by
    rw [everyExp]; simp only [conOk] at h; simp [oneConCheck, everyExp_of_conOk ht e h]
  | .handle e cs, h | .mat e cs, h => by
    rw [everyExp]; simp only [conOk, Bool.and_eq_true] at h
    simp [oneConCheck, everyExp_of_conOk ht e h.1, everyExpClauses_of_conOk ht cs h.2]
  | .con n es, h => by
    rw [everyExp]; simp only [conOk, Bool.and_eq_true] at h
    simp [oneConCheck_of ht n es h.1, everyExpList_of_conOk ht es h.2]
  | .app _ es, h => by
    rw [everyExp]; simp only [conOk] at h; simp [oneConCheck, everyExpList_of_conOk ht es h]
  | .log _ a b, h | .let_ _ a b, h => by
    rw [everyExp]; simp only [conOk, Bool.and_eq_true] at h
    simp [oneConCheck, everyExp_of_conOk ht a h.1, everyExp_of_conOk ht b h.2]
  | .if_ a b c, h => by
    rw [everyExp]; simp only [conOk, Bool.and_eq_true] at h
    simp [oneConCheck, everyExp_of_conOk ht a h.1.1, everyExp_of_conOk ht b h.1.2,
      everyExp_of_conOk ht c h.2]
  | .letrec fs b, h => by
    rw [everyExp]; simp only [conOk, Bool.and_eq_true] at h
    simp [oneConCheck, everyExp_of_conOk ht b h.1, everyExpFuns_of_conOk ht fs h.2]
  | .lit _, _ | .var _, _ => by rw [everyExp]; simp [oneConCheck]
theorem everyExpList_of_conOk {tbl : List (ConN × Nat)} {envC : Namespace ModN ConN (Nat × Stamp)}
    (ht : TableOk tbl envC) : ∀ es, conOkList tbl es = true → everyExpList (oneConCheck envC) es = true
  | [], _ => by rw [everyExpList]
  | e :: es, h => by
    rw [everyExpList]; simp only [conOkList, Bool.and_eq_true] at h
    simp [everyExp_of_conOk ht e h.1, everyExpList_of_conOk ht es h.2]
theorem everyExpClauses_of_conOk {tbl : List (ConN × Nat)} {envC : Namespace ModN ConN (Nat × Stamp)}
    (ht : TableOk tbl envC) : ∀ cs, conOkClauses tbl cs = true → everyExpClauses (oneConCheck envC) cs = true
  | [], _ => by rw [everyExpClauses]
  | (_, e) :: cs, h => by
    rw [everyExpClauses]; simp only [conOkClauses, Bool.and_eq_true] at h
    simp [everyExp_of_conOk ht e h.1, everyExpClauses_of_conOk ht cs h.2]
theorem everyExpFuns_of_conOk {tbl : List (ConN × Nat)} {envC : Namespace ModN ConN (Nat × Stamp)}
    (ht : TableOk tbl envC) : ∀ fs, conOkFuns tbl fs = true → everyExpFuns (oneConCheck envC) fs = true
  | [], _ => by rw [everyExpFuns]
  | (_, _, e) :: fs, h => by
    rw [everyExpFuns]; simp only [conOkFuns, Bool.and_eq_true] at h
    simp [everyExp_of_conOk ht e h.1, everyExpFuns_of_conOk ht fs h.2]
end

end ConPastel.Program
