import ConPastel.Spec
open Lean Meta

/-- Constants reachable from `root` through definition bodies, skipping proofs,
theorems and types. -/
partial def closure (root : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut out : Array Name := #[]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    match ci with
    | .thmInfo _ => continue
    | .defnInfo d =>
      -- skip propositions/types
      let isProp ← (try isProp d.type catch _ => pure false)
      if isProp then continue
      out := out.push n
      for c in d.value.getUsedConstants do
        unless seen.contains c do todo := todo.push c
    | .opaqueInfo d =>
      out := out.push n
      for c in d.value.getUsedConstants do
        unless seen.contains c do todo := todo.push c
    | .ctorInfo _ | .inductInfo _ | .recInfo _ | .quotInfo _ | .axiomInfo _ =>
      out := out.push n
  return out

def main : IO Unit := do
  initSearchPath (← findSysroot)
  pure ()

#eval show MetaM Unit from do
  let cs ← closure ``ConPastel.conLecheResult
  let env ← getEnv
  let mut byMod : Std.HashMap String Nat := {}
  let mut kinds : Std.HashMap String Nat := {}
  for c in cs do
    let m := (env.getModuleIdxFor? c).map (fun i => env.header.moduleNames[i.toNat]!.toString) |>.getD "?"
    let top := (m.splitOn ".").take 2 |> String.intercalate "."
    byMod := byMod.insert top (byMod.getD top 0 + 1)
    let k := match env.find? c with
      | some (.defnInfo _) => "def" | some (.opaqueInfo _) => "opaque" | some (.ctorInfo _) => "ctor"
      | some (.inductInfo _) => "induct" | some (.recInfo _) => "rec" | some (.axiomInfo _) => "axiom"
      | _ => "other"
    kinds := kinds.insert k (kinds.getD k 0 + 1)
  IO.println s!"total {cs.size}"
  IO.println s!"kinds {kinds.toList}"
  let sorted := byMod.toList.toArray.qsort (fun a b => a.2 > b.2)
  for (m, n) in sorted.toList.take 40 do IO.println s!"{n} {m}"

#eval show MetaM Unit from do
  let cs ← closure ``ConPastel.conLecheResult
  let env ← getEnv
  let mut aux := 0
  let mut real : Array Name := #[]
  for c in cs do
    match env.find? c with
    | some (.opaqueInfo _) | some (.axiomInfo _) | some (.quotInfo _) => IO.println s!"special: {c}"
    | _ => pure ()
    let s := c.toString
    if (s.splitOn "match_").length > 1 || (s.splitOn "_proof").length > 1 || (s.splitOn "brecOn").length > 1
       || (s.splitOn "_sunfold").length > 1 || (s.splitOn ".below").length > 1 || (s.splitOn "_unary").length > 1
       || (s.splitOn "_mutual").length > 1 || (s.splitOn "casesOn").length > 1 || (s.splitOn ".rec").length > 1
       || (s.splitOn "noConfusion").length > 1 || (s.splitOn "_cstage").length > 1 then aux := aux + 1
    else if (env.find? c).any (·.isDefinition) then real := real.push c
  IO.println s!"aux {aux}, real defs {real.size}"
  let k := real.filter (fun n => n.toString.startsWith "ConLeche")
  IO.println s!"conleche real defs {k.size}"
  let core := real.filter (fun n => !n.toString.startsWith "ConLeche")
  IO.println s!"core real defs {core.size}: {(core.toList.take 200)}"
