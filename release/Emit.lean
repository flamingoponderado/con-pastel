import ConPastel.Leche.Program
import Flapjack.CakeParser.ToSexp

/-!
# Emitting con-pastel's CakeML program as an S-expression

Run by `release/Makefile` (`make sexp`) as

    CON_PASTEL_SEXP=out.sexp lake env lean --tstack=8388608 release/Emit.lean

It writes `conPastelProg`, the program `ConPastel.conPastel_correct` is
about, in the S-expression syntax that the CakeML compiler reads with
`cake --sexp=true`. The printer is flapjack's port of CakeML's own
(`ToSexp.program`, `Sexp.render`: HOL's `ast_sexp` encoding).

`cake_program` adds the program's constants without compiled code, and Lean
does not compile constants of an imported module. So this file adds copies
(`Emit.*`, the same values with references renamed to the copies), compiles
those, and checks in the kernel that the copy *is* `conPastelProg`
(`Emit.prog_eq`), so the emitted bytes are those of the proved program.
-/

open Lean Meta Elab Command

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace ConPastel.Release

/-- The constants reachable from `root` that have no compiled code, each
after the constants its value uses. -/
partial def uncompiled (root : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let visited ← IO.mkRef ({} : NameSet)
  let out ← IO.mkRef (#[] : Array Name)
  let rec go (n : Name) : CoreM Unit := do
    if (← visited.get).contains n then return
    visited.modify (·.insert n)
    if (IR.findEnvDecl env n).isSome then return
    let some (.defnInfo d) := env.find? n | return
    for c in d.value.getUsedConstants do go c
    out.modify (·.push n)
  go root
  out.get

end ConPastel.Release

open ConPastel.Release in
run_cmd liftCoreM do
  let ns ← uncompiled ``conPastelP.prog
  let ren : NameMap Name := ns.foldl (fun m n => m.insert n (`Emit ++ n)) {}
  let rn (e : Expr) : Expr := e.replace fun
    | .const n us => (ren.find? n).map (mkConst · us)
    | _ => none
  for n in ns do
    let some (.defnInfo d) := (← getEnv).find? n | unreachable!
    let n' := `Emit ++ n
    addDecl (.defnDecl { d with name := n', value := rn d.value })
    compileDecls #[n']

/-- The copy is the proved program. -/
theorem Emit.prog_eq : Emit.conPastelP.prog = ConPastel.conPastelProg := rfl

/-- The program's S-expression, as bytes. -/
def Emit.sexpBytes : List (BitVec 8) :=
  Flapjack.CakeParser.Sexp.render (Flapjack.CakeParser.ToSexp.program Emit.conPastelP.prog)

#eval show IO Unit from do
  let some out ← IO.getEnv "CON_PASTEL_SEXP"
    | throw <| .userError "set CON_PASTEL_SEXP to the output path"
  let bs := Emit.sexpBytes
  IO.FS.writeBinFile out ⟨(bs.map (·.toNat.toUInt8)).toArray⟩
  IO.println s!"wrote {bs.length} bytes to {out}"
