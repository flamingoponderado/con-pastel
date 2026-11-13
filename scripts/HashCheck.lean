import ConPastel.Spec
open ConPastel
#eval do
  let strs := ["", "a", "ab", "abc", "abcd", "abcde", "abcdef", "abcdefg", "abcdefgh", "abcdefghi",
    "Nat.add", "hello world, this is con-pastel", "λ→∀ unicode ✓", String.ofList (List.replicate 100 'z')]
  let mut ok := true
  for s in strs do
    if String.hash s != leanStringHash s then
      ok := false; IO.println s!"MISMATCH string {s.quote}: {String.hash s} vs {leanStringHash s}"
  for (a, b) in [(0, 0), (1, 2), (12345678901234, 98765432109876), (0xffffffffffffffff, 7)] do
    let a : UInt64 := a; let b : UInt64 := b
    if mixHash a b != leanMixHash a b then
      ok := false; IO.println s!"MISMATCH mix {a} {b}"
  IO.println s!"numBits {System.Platform.numBits}, all agree: {ok}"
