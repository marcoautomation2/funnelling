import Funnelling.Soundness

namespace Funnelling.Examples

open Funnelling.High

def obj : Ty := .cls objectName []
def tA : Ty := .cls "A" []
def tB : Ty := .cls "B" []
def newA : Expr := .new "A" [] []
def newB : Expr := .new "B" [] []
def this : Expr := .var thisName

def decA : Dec :=
  { name := "A", bounds := [], sup := objectName, supArgs := [], methods := [], fields := [] }
def decB : Dec :=
  { name := "B", bounds := [], sup := objectName, supArgs := [],
    methods := [.mk [] tB "onlyB" [] newB], fields := [] }
def decBox : Dec :=
  { name := "Box", bounds := [("X", obj)], sup := objectName, supArgs := [],
    methods := [.mk [] (.var "X") "get" [] (.field this "val")], fields := [(.var "X", "val")] }
def decC1 : Dec :=
  { name := "C1", bounds := [], sup := objectName, supArgs := [],
    methods := [.mk [] tA "m" [] newA], fields := [] }
def decC2 : Dec :=
  { name := "C2", bounds := [], sup := "C1", supArgs := [], methods := [], fields := [] }

def d1 : Decls := [objectDec, decA, decB, decBox, decC1, decC2]

-- W1: the class table d1 is well formed.
theorem w1 : wfDecls d1 = true := by decide

-- W2: a method declaring two parameters named x violates A4.
def decDup : Dec :=
  { name := "Dup", bounds := [], sup := objectName, supArgs := [],
    methods := [.mk [] tA "m" [(tA, "x"), (tA, "x")] (.var "x")], fields := [] }
theorem w2 : wfDecls [objectDec, decA, decDup] = false := by decide

-- W3: an if binding the parameter x again violates A7.
def decShadow : Dec :=
  { name := "Shadow", bounds := [], sup := objectName, supArgs := [],
    methods := [.mk [] tA "m" [(tA, "x")] (.ifInst (.var "x") tA "x" (.var "x") (.var "x"))],
    fields := [] }
theorem w3 : wfDecls [objectDec, decA, decShadow] = false := by decide

-- W4: a superclass that is not declared violates A9 and A10.
def decOrphan : Dec :=
  { name := "Orphan", bounds := [], sup := "Missing", supArgs := [], methods := [], fields := [] }
theorem w4 : wfDecls [objectDec, decOrphan] = false := by decide

-- R1: rule simpleFieldFound.
theorem r1 : Step d1 (.field (.new "Box" [tA] [newA]) "val") newA :=
  Step.simpleFieldFound (dec := decBox) (vs1 := [newA]) (vs := [])
    (.tail _ (.tail _ (.tail _ (.head _)))) rfl rfl rfl rfl

-- R2: rule simpleAddSuper.
theorem r2 : Step d1 (.call (.new "C2" [] []) [] "m" [])
    (.superCall (.new "C2" [] []) (.cls "C2" []) [] "m" []) :=
  Step.simpleAddSuper rfl rfl rfl

-- R3: rule searchSuper.
theorem r3 : Step d1 (.superCall (.new "C2" [] []) (.cls "C2" []) [] "m" [])
    (.superCall (.new "C2" [] []) (.cls "C1" []) [] "m" []) :=
  Step.searchSuper (dec := decC2) (sigma := [])
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) rfl rfl rfl rfl rfl
    rfl (by decide) rfl

-- R4: rule simpleFound, with no names to rename.
theorem r4 : Step d1 (.superCall (.new "C2" [] []) (.cls "C1" []) [] "m" []) newA :=
  Step.simpleFound (dec := decC1) (mt := .mk [] tA "m" [] newA) (sigma := [])
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) rfl rfl rfl rfl rfl (.head _)
    (Exists.intro [] (And.intro rfl rfl))
    rfl rfl

-- R5: rule ctx, inside the receiver of a call.
theorem r5 : Step d1 (.call (.field (.new "Box" [tA] [newA]) "val") [] "m" [])
    (.call newA [] "m" []) :=
  Step.ctx (E := .callRecv .hole [] "m" []) rfl r1

-- R11: three steps, new C2<>().m() reduces to new A<>().
theorem r11 : Steps d1 (.call (.new "C2" [] []) [] "m" []) newA :=
  Steps.step r2 (Steps.step r3 (Steps.step r4 Steps.refl))

-- R6: rules ifThen and ifElse.
theorem r6Then : Step d1 (.ifInst newA tA "x" (.var "x") newB) newA :=
  Step.ifThen (c' := "A") (ts := []) (ts' := []) (x := "x") (e1 := .var "x") (e1' := .var "x")
    (e2 := newB) (tv := tA) rfl rfl .refl
    (Exists.intro [] (And.intro rfl rfl))

theorem r6Else : Step d1 (.ifInst newA tB "x" (.var "x") newB) newB := by
  sorry

def tFoo (t : Ty) : Ty := .cls "Foo" [t]
def decFoo : Dec :=
  { name := "Foo", bounds := [("X", obj)], sup := objectName, supArgs := [],
    methods := [.mk [] (.var "X") "x" [] (.call this [] "x" [])], fields := [] }
def myFooBody : Expr :=
  .newLocal "MyFoo" [.funnel "Y"] "Foo" [.var "Y"] [] [.mk [] (.var "Y") "x" [] (.var "y")]
def mkMethod : Method := .mk [("Y", obj)] (tFoo (.var "Y")) "mk" [(.var "Y", "y")] myFooBody
def decMaker : Dec :=
  { name := "Maker", bounds := [], sup := objectName, supArgs := [], methods := [mkMethod], fields := [] }

def d2 : Decls := [objectDec, decA, decB, decFoo, decMaker]

-- W5: the class table d2, with the funnelled local class MyFoo, is well formed.
theorem w5 : wfDecls d2 = true := by decide

def vLocal : Expr := .newLocal "MyFoo" [.ground tA] "Foo" [tA] [] [.mk [] tA "x" [] newA]

-- R7: rule simpleFound renames Y and y into Y1 and y1, then replaces Y1 and y1.
theorem r7 : Step d2 (.superCall (.new "Maker" [] []) (.cls "Maker" []) [tA] "mk" [newA]) vLocal :=
  Step.simpleFound (dec := decMaker) (mt := mkMethod)
    (delta' := [("Y1", obj)]) (t0 := tFoo (.var "Y1")) (ps := [(.var "Y1", "y1")])
    (e0 := .newLocal "MyFoo" [.funnel "Y1"] "Foo" [.var "Y1"] []
      [.mk [] (.var "Y1") "x" [] (.var "y1")])
    (sigma := [("Y1", tA)])
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) rfl rfl rfl rfl rfl (.head _)
    (Exists.intro ["Y1", "y1"] (And.intro rfl rfl)) rfl rfl

-- R8: rule innerFound.
theorem r8 : Step d2 (.call vLocal [] "x" []) newA :=
  Step.innerFound (mt := .mk [] tA "x" [] newA) (delta' := []) (t0 := tA) (ps := []) (e0 := newA)
    (sigma := []) rfl rfl rfl (.head _) (Exists.intro [] (And.intro rfl rfl)) rfl rfl

-- R9: rule innerSuper.
theorem r9 : Step d2 (.call vLocal [] "other" []) (.superCall vLocal (tFoo tA) [] "other" []) :=
  Step.innerSuper rfl rfl rfl rfl

-- R10: rule innerFieldSuper.
theorem r10 : Step d2 (.field vLocal "f") (.field (.new "Foo" [tA] []) "f") :=
  Step.innerFieldSuper rfl

-- T1: new Box<A<>>(new A<>()).val has type A<>.
theorem kindA : Kind d1 [] tA :=
  Kind.cls (delta0 := []) (ts0 := []) (sigma := []) rfl (by intro t h; cases h) rfl
    (by intro p h; cases h)

theorem subAObj : Sub d1 [] tA obj :=
  Sub.inherit (dec := decA) (sigma := []) (.tail _ (.head _)) rfl rfl .refl

theorem kindBoxA : Kind d1 [] (.cls "Box" [tA]) :=
  Kind.cls (delta0 := [("X", obj)]) (ts0 := [tA]) (sigma := [("X", tA)]) rfl
    (by intro t h; cases h with
      | head => exact kindA
      | tail _ h => cases h)
    rfl
    (by intro p h; cases h with
      | head => exact subAObj
      | tail _ h => cases h)

theorem typNewA : Typing d1 false [] [] newA tA :=
  Typing.newTop (dec := decA) (es1 := []) (es2 := []) (sigma := []) (.tail _ (.head _)) rfl kindA rfl rfl
    (by intro p h; cases h) Typing.newObject

theorem typBox : Typing d1 false [] [] (.new "Box" [tA] [newA]) (.cls "Box" [tA]) :=
  Typing.newTop (dec := decBox) (es1 := [newA]) (es2 := []) (sigma := [("X", tA)])
    (.tail _ (.tail _ (.tail _ (.head _)))) rfl kindBoxA rfl rfl
    (by intro p h; cases h with
      | head => exact typNewA
      | tail _ h => cases h)
    Typing.newObject

theorem t1 : Typing d1 false [] [] (.field (.new "Box" [tA] [newA]) "val") tA :=
  Typing.declField (dec := decBox) (t := .var "X") (sigma := [("X", tA)]) typBox
    (.tail _ (.tail _ (.tail _ (.head _)))) rfl (.head _) rfl

-- T2: new Box<A<>>(new B<>()) is ill typed: B<> is not a subtype of A<>.
theorem t2 : Not (Typing d1 false [] [] (.new "Box" [tA] [newB]) (.cls "Box" [tA])) := by
  sorry

-- C1: rule cast-down accepts the type test instanceof MyFoo<X> from Foo<X>.
theorem c1 : Cast d2 [("X", obj)] (tFoo (.var "X")) (.cls "MyFoo" [.var "X"]) :=
  Cast.down (xs := ["Y"]) (ts' := [.var "Y"])
    (Sub.inheritLocal (fs := [.funnel "Y"]) (c' := "Foo") (ts' := [.var "Y"]) (es := [])
      (ms := [.mk [] (.var "Y") "x" [] (.var "y")]) (sigma := [("Y", .var "X")])
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) rfl .refl)
    rfl
    (Sub.inheritLocal (fs := [.funnel "Y"]) (c' := "Foo") (ts' := [.var "Y"]) (es := [])
      (ms := [.mk [] (.var "Y") "x" [] (.var "y")]) (sigma := [("Y", .var "Y")])
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) rfl .refl)
    (by intro x h; cases h with
      | head => exact .head _
      | tail _ h => cases h)

-- C2: rule cast-down rejects the type test instanceof MyFoo<X> from Object<>.
theorem c2 : Not (Cast d2 [("X", obj)] obj (.cls "MyFoo" [.var "X"])) := by
  sorry

-- M1: the class Maker is Ok under funnelled typing.
theorem m1 : ClassOk d2 false decMaker := by
  sorry

def brokenBody : Expr :=
  .ifInst (.var "other") (.cls "MyFoo" []) "w" (.var "w")
    (.newLocal "MyFoo" [] "Foo" [.var "X"] [] [.mk [] (.var "X") "x" [] (.var "x")])
def decBroken : Dec :=
  { name := "Broken", bounds := [], sup := objectName, supArgs := [],
    methods := [.mk [("X", obj)] (tFoo (.var "X")) "m" [(obj, "other"), (.var "X", "x")] brokenBody],
    fields := [] }

def d3 : Decls := [objectDec, decA, decB, decFoo, decBroken]

def eA : Expr := .call (.new "Broken" [] []) [tA] "m" [.new "Foo" [tA] [], newA]
def brokenMain : Expr :=
  .call (.call (.call (.new "Broken" [] []) [tB] "m" [eA, newB]) [] "x" []) [] "onlyB" []

def Stuck (d : Decls) (e : Expr) : Prop := e.isValue = false /\ forall e', Not (Step d e e')

-- W6: Example 1 in the core language is well formed.
theorem w6 : wfDecls d3 = true /\ wfExpr brokenMain = true := by decide

-- J1: Example 1 is well typed under Java typing (rule new-local-java).
theorem j1 : ProgOk d3 true brokenMain := by
  sorry

-- J2: Example 1 reduces to new A<>().onlyB(), which is stuck.
theorem j2 : Steps d3 brokenMain (.call newA [] "onlyB" []) /\ Stuck d3 (.call newA [] "onlyB" []) := by
  sorry

-- N1: Example 1 is ill typed under funnelled typing.
theorem n1 : Not (ProgOk d3 false brokenMain) := by
  sorry

def decLeaker : Dec :=
  { name := "Leaker", bounds := [], sup := objectName, supArgs := [],
    methods := [
      .mk [("Y", obj)] (.cls "MyFoo2" []) "mk2" [(.var "Y", "y")]
        (.newLocal "MyFoo2" [] "Foo" [.var "Y"] [] [.mk [] (.var "Y") "x" [] (.var "y")]),
      .mk [("Y", obj)] (tFoo (.var "Y")) "leak" [(.cls "MyFoo2" [], "z")] (.var "z")],
    fields := [] }

def d4 : Decls := [objectDec, decA, decB, decFoo, decLeaker]

-- W7: the class table d4 is well formed.
theorem w7 : wfDecls d4 = true := by decide

-- L1: the method leak is well typed under Java typing.
theorem l1 : ClassOk d4 true decLeaker := by
  sorry

-- L2: the method mk2 is ill typed under funnelled typing.
theorem l2 : Not (ClassOk d4 false decLeaker) := by
  sorry

end Funnelling.Examples
