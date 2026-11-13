import ConPastel.Spec
open Lean Meta

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
    out := out.push n
    let deps := match ci with
      | .defnInfo d => d.value.getUsedConstants ++ d.type.getUsedConstants
      | .opaqueInfo d => d.value.getUsedConstants
      | .ctorInfo c => c.type.getUsedConstants
      | .inductInfo i => i.type.getUsedConstants ++ i.ctors.toArray
      | _ => #[]
    if let .thmInfo _ := ci then continue
    for c in deps do
      unless seen.contains c do todo := todo.push c
  return out

#eval show MetaM Unit from do
  let cs ← closure ``ConPastel.conLecheResult
  let env ← getEnv
  let mut n := 0
  let mut nested := #[]
  let mut params := 0
  let mut indexed := #[]
  for c in cs do
    if let some (.inductInfo ii) := env.find? c then
      if (← isProp ii.type) || (← forallTelescope ii.type fun _ b => pure b.isProp) then continue
      n := n + 1
      if ii.isNested then nested := nested.push c
      if ii.numParams > 0 then params := params + 1
      if ii.numIndices > 0 then indexed := indexed.push c
  IO.println s!"data inductives: {n}, parameterized: {params}"
  IO.println s!"nested: {nested.toList}"
  IO.println s!"indexed: {indexed.toList}"
