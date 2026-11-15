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
