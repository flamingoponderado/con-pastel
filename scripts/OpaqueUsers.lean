import ConPastel.Spec
open Lean Meta

partial def reach (root : Name) : MetaM (Std.HashMap Name (Array Name)) := do
  -- parent map: for each constant, which constants reference it (within closure)
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut parents : Std.HashMap Name (Array Name) := {}
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let v? := match ci with
      | .defnInfo d => some d.value | .opaqueInfo d => some d.value | _ => none
    if let .thmInfo _ := ci then continue
    if let .defnInfo d := ci then
      if (← (try isProp d.type catch _ => pure false)) then continue
    if let some v := v? then
      for c in v.getUsedConstants do
        parents := parents.insert c ((parents.getD c #[]).push n)
        unless seen.contains c do todo := todo.push c
  return parents

#eval show MetaM Unit from do
  let parents ← reach ``ConPastel.conLecheResult
  let targets := [``String.hash, ``mixHash, ``String.Internal.append, ``ConLeche.Expr.hasStrLitGo,
    ``System.Platform.getNumBits, ``Classical.choice, ``Quot.lift]
  for t in targets do
    -- walk up to first ConLeche ancestors
    let mut frontier : Array Name := #[t]
    let mut seen : NameSet := {}
    let mut hits : Array Name := #[]
    while h : frontier.size > 0 do
      let n := frontier.back
      frontier := frontier.pop
      if seen.contains n then continue
      seen := seen.insert n
      if n.toString.startsWith "ConLeche" && n != t then
        hits := hits.push n
        continue
      for p in parents.getD n #[] do frontier := frontier.push p
    IO.println s!"{t}: {hits.size} con-leche callers: {hits.toList.take 25}"

#eval show MetaM Unit from do
  let parents ← reach ``ConPastel.conLecheResult
  for t in [``String.Internal.append, ``Classical.choice, ``System.Platform.getNumBits] do
    IO.println s!"direct users of {t}: {(parents.getD t #[]).toList}"
    for p in parents.getD t #[] do
      IO.println s!"   users of {p}: {((parents.getD p #[]).toList.take 8)}"
