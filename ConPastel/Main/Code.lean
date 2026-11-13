import ConPastel.Translator.Meta.Unit

/-!
# The CakeML main program

After the translated units, the program
1. allocates a 2-byte buffer (`buf`);
2. reads the whole input with the recursive `readAll`, one byte per `read`
   call, into a list of byte values (most recent first);
3. reverses it (`revApp`, a translated unit) and calls `entry`, the
   translated checker on the list of input bytes;
4. writes `accepted\n` or `rejected\n`.
-/

namespace ConPastel.Main
open Flapjack Flapjack.AstHOL Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
open ConPastel.Translator

/-- `revApp xs acc = xs.reverse ++ acc`, translated as a unit. -/
def revApp : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: xs, acc => revApp xs (x :: acc)

def bufName : String := "con-pastel.buf"
def readAllName : String := "con-pastel.readAll"
def resultName : String := "con-pastel.result"

def var (s : String) : Exp := .var (.short (ofString s))

/-- `fn acc => (#(read) "" buf; if buf[0] = 0w then acc
                               else readAll (w2n buf[1] :: acc))` -/
def readAllBody : Exp :=
  .let_ none (.app (.ffi (ofString "read")) [.lit (.strLit (ofString "")), var bufName])
    (.if_ (.app .equality [.app .aw8sub [var bufName, .lit (.intLit 0)], .lit (.word8 0)])
      (var "acc")
      (.app .opapp [var readAllName,
        .con (some (.short (ofString "::")))
          [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]], var "acc"]]))

def mainDecs (entryName revName : String) : List Dec :=
  [.dlet unknownLoc (.pvar (ofString bufName)) (.app .aw8alloc [.lit (.intLit 2), .lit (.word8 0)]),
   .dletrec unknownLoc [(ofString readAllName, ofString "acc", readAllBody)],
   .dlet unknownLoc (.pvar (ofString resultName))
     (.app .opapp [var entryName,
       .app .opapp [var revName,
         .con none [.app .opapp [var readAllName, .con (some (.short (ofString "[]"))) []],
           .con (some (.short (ofString "[]"))) []]]]),
   .dlet unknownLoc .pany
     (.app (.ffi (ofString "write"))
       [.if_ (var resultName) (.lit (.strLit (ofString "accepted\n"))) (.lit (.strLit (ofString "rejected\n"))),
        var bufName])]

end ConPastel.Main

namespace ConPastel.Main
cake_unit revApp
end ConPastel.Main
