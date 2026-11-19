import ConLeche.Kernel.Expr
import ConPastel.Translator.Meta.Primitive

/-!
# Shared `Expr` blobs as decoded data

con-leche's pinned Nat-operation data (`ConLeche/Kernel/NatOpPins.lean`:
`nat…DeclPin_v<i>`, `nat…CertProofs_v<i>_<j>`, `nat…DeclPinType_v<i>_<j>`)
are spliced as long `let`-chains, one binder per shared subobject. Translating
such a chain binder by binder costs time quadratic in its length (thousands of
binders), so each blob `c` is instead translated as

```
c = c.blob := decodeBlob c.blobData root
```

where `c.blobData : List Ent` is the share table as plain data and `decodeBlob`
— translated once — rebuilds the value. The equation `c.blob_eq` is checked by
the kernel (`Eq.refl`), and `cake_replace c c.blob c.blob_eq` makes the
translator use it.

References are de Bruijn indices into the table built so far (most recent
entry first), exactly the `let`-chain's own indices.
-/

namespace ConPastel.Leche.Blob
open ConLeche

/-- A reference to an earlier entry, or an inline anonymous name / zero level. -/
inductive Ref | idx (i : Nat) | anon | lzero

/-- One share-table entry: a constructor application over references. -/
inductive Ent
  | nameStr (p : Ref) (s : String) | nameNum (p : Ref) (i : Nat)
  | levSucc (u : Ref) | levMax (u v : Ref) | levImax (u v : Ref) | levParam (n : Ref)
  | bvar (i : Nat) | fvar (idx : Nat) (ty : Ref) | sort (u : Ref)
  | const (n : Ref) (us : List Ref) | app (f a : Ref) | lam (ty b : Ref)
  | forallE (ty b : Ref) | letE (ty v b : Ref) | litNat (v : Nat) | litStr (s : String)
  | proj (s : Ref) (i : Nat) (e : Ref)

/-- A decoded entry. -/
inductive Obj | n (x : Name) | l (x : Level) | e (x : Expr)

def nth : List Obj → Nat → Option Obj
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

def getN (t : List Obj) : Ref → Name
  | .idx i => match nth t i with | some (.n x) => x | _ => .anonymous
  | _ => .anonymous
def getL (t : List Obj) : Ref → Level
  | .idx i => match nth t i with | some (.l x) => x | _ => .zero
  | _ => .zero
def getE (t : List Obj) : Ref → Expr
  | .idx i => match nth t i with | some (.e x) => x | _ => .bvar 0
  | _ => .bvar 0

def getLs (t : List Obj) : List Ref → List Level
  | [] => []
  | r :: rs => getL t r :: getLs t rs

def Ent.decode (t : List Obj) : Ent → Obj
  | .nameStr p s => .n (.str (getN t p) s)
  | .nameNum p i => .n (.num (getN t p) i)
  | .levSucc u => .l (.succ (getL t u))
  | .levMax u v => .l (.max (getL t u) (getL t v))
  | .levImax u v => .l (.imax (getL t u) (getL t v))
  | .levParam n => .l (.param (getN t n))
  | .bvar i => .e (.bvar i)
  | .fvar i ty => .e (.fvar i (getE t ty))
  | .sort u => .e (.sort (getL t u))
  | .const n us => .e (.const (getN t n) (getLs t us))
  | .app f a => .e (.app (getE t f) (getE t a))
  | .lam ty b => .e (.lam (getE t ty) (getE t b))
  | .forallE ty b => .e (.forallE (getE t ty) (getE t b))
  | .letE ty v b => .e (.letE (getE t ty) (getE t v) (getE t b))
  | .litNat v => .e (.lit (.natVal v))
  | .litStr s => .e (.lit (.strVal s))
  | .proj s i e => .e (.proj (getN t s) i (getE t e))

def build (t : List Obj) : List Ent → List Obj
  | [] => t
  | e :: es => build (e.decode t :: t) es

/-- The value of a blob: its table, decoded, at the root reference. -/
def decodeBlob (es : List Ent) (root : Ref) : Expr := getE (build [] es) root

/-! ## Fast decoding

`build` keeps the decoded entries in a list and every reference is an `nth`
on it: decoding is quadratic in the table size (the pinned Nat-operation data
has tables of thousands of entries, and its decode was most of the checker's
start-up time). `decodeBlobF` keeps them in a binary trie keyed by position
(entry `k` at key `k + 1`, read bit by bit from the least significant end), so
each reference costs `log` of the table size. It is proved equal to
`decodeBlob`, which stays what the kernel checks the blobs against. -/

/-- A trie on positive keys: key `1` at the root, `2m` under the left child at
`m`, `2m+1` under the right child at `m`. -/
inductive Tab
  | nil
  | node (v : Option Obj) (l r : Tab)

def Tab.get : Tab → Nat → Option Obj
  | .nil, _ => none
  | .node v l r, m =>
    if m = 1 then v else if m < 2 then none
    else if m % 2 = 0 then l.get (m / 2) else r.get (m / 2)

/-- The root and children of a trie (`nil` reads as an empty node). -/
def Tab.parts : Tab → Option Obj × Tab × Tab
  | .nil => (none, .nil, .nil)
  | .node v l r => (v, l, r)

/-- Store at key `m`; the fuel `f` bounds the depth (`m < 2 ^ f` suffices). -/
def Tab.set : Nat → Tab → Nat → Obj → Tab
  | 0, t, _, _ => t
  | f + 1, t, m, o =>
    if m = 1 then .node (some o) t.parts.2.1 t.parts.2.2
    else if m < 2 then t
    else if m % 2 = 0 then .node t.parts.1 (Tab.set f t.parts.2.1 (m / 2) o) t.parts.2.2
    else .node t.parts.1 t.parts.2.1 (Tab.set f t.parts.2.2 (m / 2) o)

theorem Tab.get_parts (t : Tab) (m : Nat) :
    t.get m = (Tab.node t.parts.1 t.parts.2.1 t.parts.2.2).get m := by
  cases t with
  | nil => simp [Tab.parts, Tab.get]
  | node v l r => rfl

theorem Tab.get_zero (t : Tab) : t.get 0 = none := by
  cases t <;> simp [Tab.get]

theorem Tab.get_set : ∀ (f : Nat) (t : Tab) (m m' : Nat) (o : Obj), 1 ≤ m → m < 2 ^ f →
    (Tab.set f t m o).get m' = if m' = m then some o else t.get m'
  | 0, t, m, m', o, h1, h2 => by simp at h2; omega
  | f + 1, t, m, m', o, h1, h2 => by
    rw [Tab.get_parts t m']
    simp only [Tab.set]
    by_cases hm : m = 1
    · subst hm; simp only [ite_true]; simp only [Tab.get]
      by_cases h' : m' = 1 <;> simp [h']
    · simp only [hm, ite_false]
      have hm2 : ¬ m < 2 := by omega
      simp only [hm2, ite_false]
      have hlt : m / 2 < 2 ^ f := by rw [Nat.pow_succ] at h2; omega
      have hge : 1 ≤ m / 2 := by omega
      by_cases he : m % 2 = 0
      · simp only [he, ite_true, Tab.get]
        by_cases h' : m' = 1
        · simp [h']; omega
        · simp only [h', ite_false]
          by_cases h2' : m' < 2
          · simp [h2']; omega
          · simp only [h2', ite_false]
            by_cases he' : m' % 2 = 0
            · simp only [he', ite_true, Tab.get_set f _ (m / 2) (m' / 2) o hge hlt]
              by_cases hq : m' / 2 = m / 2
              · simp [hq]; omega
              · simp [hq]; omega
            · simp only [he', ite_false]
              have : m' ≠ m := by omega
              simp [this]
      · simp only [he, ite_false, Tab.get]
        by_cases h' : m' = 1
        · simp [h']; omega
        · simp only [h', ite_false]
          by_cases h2' : m' < 2
          · simp [h2']; omega
          · simp only [h2', ite_false]
            by_cases he' : m' % 2 = 0
            · simp only [he', ite_true]
              have : m' ≠ m := by omega
              simp [this]
            · simp only [he', ite_false, Tab.get_set f _ (m / 2) (m' / 2) o hge hlt]
              by_cases hq : m' / 2 = m / 2
              · simp [hq]; omega
              · simp [hq]; omega

/-! Decoding over a lookup function (`nth t` for `build`, the trie for `buildF`). -/

def getNW (look : Nat → Option Obj) : Ref → Name
  | .idx i => match look i with | some (.n x) => x | _ => .anonymous
  | _ => .anonymous
def getLW (look : Nat → Option Obj) : Ref → Level
  | .idx i => match look i with | some (.l x) => x | _ => .zero
  | _ => .zero
def getEW (look : Nat → Option Obj) : Ref → Expr
  | .idx i => match look i with | some (.e x) => x | _ => .bvar 0
  | _ => .bvar 0
def getLsW (look : Nat → Option Obj) : List Ref → List Level
  | [] => []
  | r :: rs => getLW look r :: getLsW look rs

def Ent.decodeW (look : Nat → Option Obj) : Ent → Obj
  | .nameStr p s => .n (.str (getNW look p) s)
  | .nameNum p i => .n (.num (getNW look p) i)
  | .levSucc u => .l (.succ (getLW look u))
  | .levMax u v => .l (.max (getLW look u) (getLW look v))
  | .levImax u v => .l (.imax (getLW look u) (getLW look v))
  | .levParam n => .l (.param (getNW look n))
  | .bvar i => .e (.bvar i)
  | .fvar i ty => .e (.fvar i (getEW look ty))
  | .sort u => .e (.sort (getLW look u))
  | .const n us => .e (.const (getNW look n) (getLsW look us))
  | .app f a => .e (.app (getEW look f) (getEW look a))
  | .lam ty b => .e (.lam (getEW look ty) (getEW look b))
  | .forallE ty b => .e (.forallE (getEW look ty) (getEW look b))
  | .letE ty v b => .e (.letE (getEW look ty) (getEW look v) (getEW look b))
  | .litNat v => .e (.lit (.natVal v))
  | .litStr s => .e (.lit (.strVal s))
  | .proj s i e => .e (.proj (getNW look s) i (getEW look e))

theorem getN_W (t : List Obj) (r : Ref) : getN t r = getNW (nth t) r := by cases r <;> rfl
theorem getL_W (t : List Obj) (r : Ref) : getL t r = getLW (nth t) r := by cases r <;> rfl
theorem getE_W (t : List Obj) (r : Ref) : getE t r = getEW (nth t) r := by cases r <;> rfl
theorem getLs_W (t : List Obj) : ∀ rs, getLs t rs = getLsW (nth t) rs
  | [] => rfl
  | r :: rs => by simp only [getLs, getLsW, getLs_W t rs, getL_W]
theorem Ent.decode_W (t : List Obj) (e : Ent) : e.decode t = e.decodeW (nth t) := by
  cases e <;> simp only [Ent.decode, Ent.decodeW, getN_W, getL_W, getE_W, getLs_W]

/-- The trie version of `build`: `n` entries so far, at keys `1 … n`. -/
def buildF (tab : Tab) (n : Nat) : List Ent → Tab × Nat
  | [] => (tab, n)
  | e :: es =>
    buildF (tab.set (n + 1) (n + 1) (e.decodeW (fun i => tab.get (n - i)))) (n + 1) es

def decodeBlobF (es : List Ent) (root : Ref) : Expr :=
  let p := buildF .nil 0 es
  getEW (fun i => p.1.get (p.2 - i)) root

theorem nth_ge : ∀ (t : List Obj) (i : Nat), t.length ≤ i → nth t i = none
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: xs, i + 1, h => by simp only [nth]; exact nth_ge xs i (by simp at h; omega)

/-- The trie at `n` represents the list (most recent entry first). -/
def TabRep (tab : Tab) (n : Nat) (t : List Obj) : Prop :=
  t.length = n ∧ ∀ i, tab.get (n - i) = nth t i

theorem buildF_rep : ∀ (es : List Ent) (tab : Tab) (n : Nat) (t : List Obj), TabRep tab n t →
    TabRep (buildF tab n es).1 (buildF tab n es).2 (build t es)
  | [], tab, n, t, h => h
  | e :: es, tab, n, t, ⟨hl, hg⟩ => by
    simp only [buildF, build]
    have hlook : (fun i => tab.get (n - i)) = nth t := funext hg
    rw [hlook, ← Ent.decode_W]
    apply buildF_rep es
    refine ⟨by simp [hl], fun i => ?_⟩
    rw [Tab.get_set _ _ _ _ _ (by omega) (Nat.lt_two_pow_self)]
    cases i with
    | zero => simp [nth]
    | succ j =>
      simp only [nth]
      by_cases hj : j < n
      · have : n + 1 - (j + 1) ≠ n + 1 := by omega
        simp only [this, ite_false]
        have := hg j; rw [show n + 1 - (j + 1) = n - j by omega]; exact this
      · have : n + 1 - (j + 1) = 0 := by omega
        simp only [this, Tab.get_zero]
        split <;> first | omega | exact (nth_ge t j (by omega)).symm

theorem decodeBlob_eq_F (es : List Ent) (root : Ref) : decodeBlob es root = decodeBlobF es root := by
  have h := buildF_rep es .nil 0 [] ⟨rfl, fun i => by simp [Tab.get, nth]⟩
  simp only [decodeBlob, decodeBlobF, getE_W]
  congr 1
  exact (funext h.2).symm

open Lean Meta Elab Command

/-- The `let`-chain value of a blob as `(entries : List Ent, root : Ref)`. -/
partial def invert (v : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let ref (a : Lean.Expr) : MetaM Lean.Expr := do
    match a with
    | .bvar j => return mkApp (mkConst ``Ref.idx) (mkRawNatLit j)
    | .const ``ConLeche.Name.anonymous _ => return mkConst ``Ref.anon
    | .const ``ConLeche.Level.zero _ => return mkConst ``Ref.lzero
    | _ => throwError "cake_blob: unexpected reference {a}"
  let rec refs (a : Lean.Expr) : MetaM Lean.Expr := do
    match a.getAppFnArgs with
    | (``List.nil, _) => return mkApp (mkConst ``List.nil [0]) (mkConst ``Ref)
    | (``List.cons, #[_, h, t]) => return mkApp3 (mkConst ``List.cons [0]) (mkConst ``Ref) (← ref h) (← refs t)
    | _ => throwError "cake_blob: unexpected level list {a}"
  let lit (a : Lean.Expr) : MetaM Lean.Expr := do
    unless a.isLit do throwError "cake_blob: unexpected literal {a}"
    return a
  let ent (x : Lean.Expr) : MetaM Lean.Expr := do
    let (c, as) := x.getAppFnArgs
    match c, as with
    | ``ConLeche.Name.str, #[p, s] => return mkApp2 (mkConst ``Ent.nameStr) (← ref p) (← lit s)
    | ``ConLeche.Name.num, #[p, i] => return mkApp2 (mkConst ``Ent.nameNum) (← ref p) (← lit i)
    | ``ConLeche.Level.succ, #[u] => return mkApp (mkConst ``Ent.levSucc) (← ref u)
    | ``ConLeche.Level.max, #[u, w] => return mkApp2 (mkConst ``Ent.levMax) (← ref u) (← ref w)
    | ``ConLeche.Level.imax, #[u, w] => return mkApp2 (mkConst ``Ent.levImax) (← ref u) (← ref w)
    | ``ConLeche.Level.param, #[n] => return mkApp (mkConst ``Ent.levParam) (← ref n)
    | ``ConLeche.Expr.bvar, #[i] => return mkApp (mkConst ``Ent.bvar) (← lit i)
    | ``ConLeche.Expr.fvar, #[i, t] => return mkApp2 (mkConst ``Ent.fvar) (← lit i) (← ref t)
    | ``ConLeche.Expr.sort, #[u] => return mkApp (mkConst ``Ent.sort) (← ref u)
    | ``ConLeche.Expr.const, #[n, us] => return mkApp2 (mkConst ``Ent.const) (← ref n) (← refs us)
    | ``ConLeche.Expr.app, #[f, a] => return mkApp2 (mkConst ``Ent.app) (← ref f) (← ref a)
    | ``ConLeche.Expr.lam, #[t, b] => return mkApp2 (mkConst ``Ent.lam) (← ref t) (← ref b)
    | ``ConLeche.Expr.forallE, #[t, b] => return mkApp2 (mkConst ``Ent.forallE) (← ref t) (← ref b)
    | ``ConLeche.Expr.letE, #[t, w, b] => return mkApp3 (mkConst ``Ent.letE) (← ref t) (← ref w) (← ref b)
    | ``ConLeche.Expr.lit, #[l] =>
      match l.getAppFnArgs with
      | (``ConLeche.Literal.natVal, #[n]) => return mkApp (mkConst ``Ent.litNat) (← lit n)
      | (``ConLeche.Literal.strVal, #[s]) => return mkApp (mkConst ``Ent.litStr) (← lit s)
      | _ => throwError "cake_blob: unexpected literal {l}"
    | ``ConLeche.Expr.proj, #[s, i, e] => return mkApp3 (mkConst ``Ent.proj) (← ref s) (← lit i) (← ref e)
    | _, _ => throwError "cake_blob: unexpected entry {x}"
  let mut cur := v
  let mut ents : Array Lean.Expr := #[]
  while true do
    match cur with
    | .letE _ _ val b _ =>
      ents := ents.push (← ent val)
      cur := b
    | _ => break
  let root ← ref cur
  let lst := ents.foldr (fun e acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Ent) e acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Ent))
  return (lst, root)

/-- Is `c` a blob: a closed `ConLeche.Expr` definition whose value is a `let`-chain? -/
def isBlob (ci : ConstantInfo) : Bool :=
  ci.levelParams.isEmpty && ci.type.isConstOf ``ConLeche.Expr &&
    match ci with
    | .defnInfo d => d.value.isLet
    | _ => false

/-- Register blob `c`: `c.blobData`, `c.blob`, the kernel-checked `c.blob_eq : c = c.blob`,
and the replacement. -/
def registerBlob (c : Lean.Name) : TermElabM Unit := do
  let ci ← getConstInfo c
  unless isBlob ci do throwError "cake_blob: {c} is not a let-chain Expr blob"
  let (lst, root) ← invert ci.value!
  let dataName := c ++ `blobData
  let blobName := c ++ `blob
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Ent)
  addDecl (.defnDecl { name := dataName, levelParams := [], type := lty, value := lst, hints := .abbrev, safety := .safe })
  let rhs := mkApp2 (mkConst ``decodeBlob) (mkConst dataName) root
  addDecl (.defnDecl { name := blobName, levelParams := [], type := mkConst ``ConLeche.Expr, value := rhs, hints := .regular 0, safety := .safe })
  let ty ← mkEq (mkConst c) (mkConst blobName)
  let pf ← mkEqRefl (mkConst c)
  addDecl (.thmDecl { name := c ++ `blob_eq, levelParams := [], type := ty, value := pf })
  modifyEnv fun env => ConPastel.Translator.Meta.replaceExt.addEntry env (c, blobName, c ++ `blob_eq)

/-- `cake_blob c`: translate the blob `c` through `decodeBlob`. -/
elab "cake_blob " c:ident : command => liftTermElabM do
  registerBlob (← realizeGlobalConstNoOverloadWithInfo c)

/-- `cake_blobs "suffix"`: `cake_blob` every blob of the `ConLeche` namespace whose
name contains `suffix` (e.g. a pin variant `_v0`). -/
elab "cake_blobs " s:str : command => liftTermElabM do
  let sfx := s.getString
  let mut cs : Array Lean.Name := #[]
  for (n, ci) in (← getEnv).constants.toList do
    if (`ConLeche).isPrefixOf n && (n.toString.splitOn sfx).length > 1 && isBlob ci then
      cs := cs.push n
  for c in cs.qsort Lean.Name.lt do
    registerBlob c
  logInfo m!"cake_blobs {sfx}: {cs.size} blobs"

end ConPastel.Leche.Blob
