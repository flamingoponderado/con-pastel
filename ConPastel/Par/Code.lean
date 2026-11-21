import ConPastel.Main.Code

/-!
# The CakeML main program of the parallel checker

After the translated units, the program
1. allocates the 2-byte buffer `buf` and reads the whole input with `readAll`, as the default
   program does (`ConPastel.Main.mainDecs`);
2. runs the first phase, `p = phase1 input` (parse, prepare, `buildIndex`);
3. allocates the 9-byte job buffer `jb`;
4. if the first phase failed, writes `rejected\n`. Otherwise it calls `spawn`, which forks the
   workers: in the parent `jb[0] = 0`, in a worker `jb[0] = 1`.
   * A worker loops (`work`): `claim` puts the next index in `jb[1..8]`; `c = jobCode p jb[1..8]`;
     `report` with configuration `"1"`, `"2"` or `"3"` (the code; `jb` still holds the index).
     It stops after reporting `3` (no such job).
   * The parent reads the table of codes with `readTable` (the `results` call, `read`'s
     protocol), and `v = verdictCode p table`: `0` writes `accepted\n`, `1` writes
     `rejected\n`, anything else calls `abort`.

The loops `readAll` and `readTable` have the same body (`loopBody`), on different FFI calls.
-/

namespace ConPastel.Par
open Flapjack Flapjack.AstHOL Flapjack.Basis.Pure.MlString Flapjack.Misc.Location
open ConPastel.Main

def jbName : String := "con-pastel.jb"
def readTableName : String := "con-pastel.readTable"
def workName : String := "con-pastel.work"
def pName : String := "con-pastel.p"

/-- `fn acc => (#(ffi) "" buf; if buf[0] = 0w then acc else fname (w2n buf[1] :: acc))` -/
def loopBody (ffi fname : String) : Exp :=
  .let_ none (.app (.ffi (ofString ffi)) [.lit (.strLit (ofString "")), var bufName])
    (.if_ (.app .equality [.app .aw8sub [var bufName, .lit (.intLit 0)], .lit (.word8 0)])
      (var "acc")
      (.app .opapp [var fname,
        .con (some (.short (ofString "::")))
          [.app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var bufName, .lit (.intLit 1)]], var "acc"]]))

theorem readAllBody_eq : readAllBody = loopBody "read" readAllName := rfl

/-- `w2n jb[i]` -/
def jbByte (i : Nat) : Exp :=
  .app (.fromTo (.wordT .w8) .intT) [.app .aw8sub [var jbName, .lit (.intLit i)]]

def consE (h t : Exp) : Exp := .con (some (.short (ofString "::"))) [h, t]
def nilE : Exp := .con (some (.short (ofString "[]"))) []

/-- `[w2n jb[1], …, w2n jb[8]]` -/
def jbBytes : Exp :=
  consE (jbByte 1) (consE (jbByte 2) (consE (jbByte 3) (consE (jbByte 4)
    (consE (jbByte 5) (consE (jbByte 6) (consE (jbByte 7) (consE (jbByte 8) nilE)))))))

def ffiCall (name conf buf : String) : Exp :=
  .app (.ffi (ofString name)) [.lit (.strLit (ofString conf)), var buf]

def strE (s : String) : Exp := .lit (.strLit (ofString s))

def intEq (x : Exp) (n : Nat) : Exp := .app .equality [x, .lit (.intLit n)]

/-- The worker loop:
`fn u => (#(claim) "" jb; let c = jobCode p [jb bytes] in
          if c = 3 then #(report) "3" jb
          else (#(report) (if c = 1 then "1" else "2") jb; work u))` -/
def workBody (jobCodeName : String) : Exp :=
  .let_ none (ffiCall "claim" "" jbName)
    (.let_ (some (ofString "c"))
      (.app .opapp [.app .opapp [var jobCodeName, var pName], jbBytes])
      (.if_ (intEq (var "c") 3)
        (ffiCall "report" "3" jbName)
        (.let_ none
          (.app (.ffi (ofString "report"))
            [.if_ (intEq (var "c") 1) (strE "1") (strE "2"), var jbName])
          (.app .opapp [var workName, var "u"]))))

/-- The parent, after `spawn`:
`let v = verdictCode p (revApp (readTable [], [])) in
 if v = 0 then write "accepted\n" else if v = 1 then write "rejected\n" else abort` -/
def parentBody (verdictName revName : String) : Exp :=
  .let_ (some (ofString "v"))
    (.app .opapp [.app .opapp [var verdictName, var pName],
      .app .opapp [var revName,
        .con none [.app .opapp [var readTableName, nilE], nilE]]])
    (.if_ (intEq (var "v") 0) (ffiCall "write" "accepted\n" bufName)
      (.if_ (intEq (var "v") 1) (ffiCall "write" "rejected\n" bufName)
        (ffiCall "abort" "" bufName)))

/-- After the first phase. -/
def dispatch (phase1OkName verdictName revName : String) : Exp :=
  .if_ (.app .opapp [var phase1OkName, var pName])
    (.let_ none (ffiCall "spawn" "" jbName)
      (.if_ (.app .equality [.app .aw8sub [var jbName, .lit (.intLit 0)], .lit (.word8 0)])
        (parentBody verdictName revName)
        (.app .opapp [var workName, .con none []])))
    (ffiCall "write" "rejected\n" bufName)

/-- **The main declarations of the parallel checker.** -/
def parMainDecs (phase1Name phase1OkName jobCodeName verdictName revName : String) : List Dec :=
  [.dlet unknownLoc (.pvar (ofString bufName)) (.app .aw8alloc [.lit (.intLit 2), .lit (.word8 0)]),
   .dletrec unknownLoc [(ofString readAllName, ofString "acc", loopBody "read" readAllName)],
   .dletrec unknownLoc [(ofString readTableName, ofString "acc", loopBody "results" readTableName)],
   .dlet unknownLoc (.pvar (ofString pName))
     (.app .opapp [var phase1Name,
       .app .opapp [var revName,
         .con none [.app .opapp [var readAllName, nilE], nilE]]]),
   .dlet unknownLoc (.pvar (ofString jbName)) (.app .aw8alloc [.lit (.intLit 9), .lit (.word8 0)]),
   .dletrec unknownLoc [(ofString workName, ofString "u", workBody jobCodeName)],
   .dlet unknownLoc .pany (dispatch phase1OkName verdictName revName)]

end ConPastel.Par
