import Funnelling.High.Declarations

namespace Funnelling.High

def nodup (xs : List Name) : Bool := decide xs.Nodup

mutual
def Expr.ifVars : Expr -> List Name
  | .var _ => []
  | .call e _ _ es => e.ifVars ++ Expr.ifVarsList es
  | .superCall e _ _ _ es => e.ifVars ++ Expr.ifVarsList es
  | .field e _ => e.ifVars
  | .new _ _ es => Expr.ifVarsList es
  | .newLocal _ _ _ _ es ms => Expr.ifVarsList es ++ Method.ifVarsList ms
  | .ifInst e0 _ x e1 e2 => x :: e0.ifVars ++ e1.ifVars ++ e2.ifVars
def Expr.ifVarsList : List Expr -> List Name
  | [] => []
  | e :: es => e.ifVars ++ Expr.ifVarsList es
def Method.ifVars : Method -> List Name
  | .mk _ _ _ _ e => e.ifVars
def Method.ifVarsList : List Method -> List Name
  | [] => []
  | m :: ms => m.ifVars ++ Method.ifVarsList ms
end

mutual
def Expr.noShadow (tvs vs : List Name) : Expr -> Bool
  | .var _ => true
  | .call e _ _ es => e.noShadow tvs vs && Expr.noShadowList tvs vs es
  | .superCall e _ _ _ es => e.noShadow tvs vs && Expr.noShadowList tvs vs es
  | .field e _ => e.noShadow tvs vs
  | .new _ _ es => Expr.noShadowList tvs vs es
  | .newLocal _ _ _ _ es ms =>
    Expr.noShadowList tvs vs es && Method.noShadowList tvs (vs.filter fun x => x != thisName) ms
  | .ifInst e0 _ x e1 e2 =>
    e0.noShadow tvs vs && !(vs.contains x) && e1.noShadow tvs (x :: vs) && e2.noShadow tvs vs
def Expr.noShadowList (tvs vs : List Name) : List Expr -> Bool
  | [] => true
  | e :: es => e.noShadow tvs vs && Expr.noShadowList tvs vs es
def Method.noShadow (tvs vs : List Name) : Method -> Bool
  | .mk delta _ _ ps e =>
    (dom delta).all (fun x => !(tvs.contains x)) &&
    (ps.map Prod.snd).all (fun x => !(vs.contains x)) &&
    e.noShadow (tvs ++ dom delta) (thisName :: vs ++ ps.map Prod.snd)
def Method.noShadowList (tvs vs : List Name) : List Method -> Bool
  | [] => true
  | m :: ms => m.noShadow tvs vs && Method.noShadowList tvs vs ms
end

def Method.params : Method -> List Name
  | .mk _ _ _ ps _ => ps.map Prod.snd

def K.funnels : K -> List Funnel
  | .top _ => []
  | .loc _ fs _ _ _ _ => fs

def K.sup : K -> Name
  | .top dec => dec.sup
  | .loc _ _ c _ _ _ => c

def Decls.methods (d : Decls) : List Method :=
  (declaredKs d).flatMap K.methods

def Expr.methods (e : Expr) : List Method := e.locals.flatMap K.methods

def superChain (d : Decls) : Nat -> Name -> List Dec
  | 0, _ => []
  | fuel + 1, c =>
    match findDec d c with
    | none => []
    | some dec => if c == objectName then [dec] else dec :: superChain d fuel dec.sup

def reachesObject (d : Decls) (c : Name) : Bool :=
  (superChain d (d.length + 1) c).any fun dec => dec.name == objectName

def objectDec : Dec := { name := objectName, bounds := [], sup := objectName, supArgs := [], methods := [], fields := [] }

def a1 (d : Decls) : Bool := nodup ((declaredKs d).map K.name)

def a2 (d : Decls) : Bool :=
  d.all fun dec => nodup ((superChain d (d.length + 1) dec.name).flatMap fun c => c.fields.map Prod.snd)

def a3 (ks : List K) : Bool := ks.all fun k => nodup (k.methods.map Method.name)

def a4 (ms : List Method) : Bool := ms.all fun m => nodup m.params

def a5 (d : Decls) (ms : List Method) : Bool :=
  d.all (fun dec => nodup (dom dec.bounds)) && ms.all fun m => nodup (dom m.bounds)

def a6 (ks : List K) : Bool := ks.all fun k => nodup (domF k.funnels)

def a7Decls (d : Decls) : Bool := d.all fun dec => Method.noShadowList (dom dec.bounds) [] dec.methods

def a8 (ms : List Method) (ifVars : List Name) : Bool :=
  ms.all (fun m => !(m.params.contains thisName)) && !(ifVars.contains thisName)

def a9 (d : Decls) : Bool :=
  (d.any fun dec => dec.name == objectName && dec.bounds.isEmpty && dec.sup == objectName &&
    dec.supArgs.isEmpty && dec.methods.isEmpty && dec.fields.isEmpty) &&
  d.all fun dec => reachesObject d dec.name

def a10 (d : Decls) : Bool := (declaredKs d).all fun k => (findDec d k.sup).isSome

def a11 (d : Decls) : Bool :=
  (declaredKs d).all fun k => k.funnels.all fun
    | .funnel _ => true
    | .ground _ => false

def groundFunnels (ks : List K) : Bool :=
  ks.all fun k => k.funnels.all fun
    | .funnel _ => true
    | .ground g => g.isGround

def wfDecls (d : Decls) : Bool :=
  a1 d && a2 d && a3 (declaredKs d) && a4 d.methods && a5 d d.methods && a6 (declaredKs d) &&
  a7Decls d && a8 d.methods (d.flatMap fun dec => Method.ifVarsList dec.methods) &&
  a9 d && a10 d && a11 d && groundFunnels (declaredKs d)

def wfExpr (e : Expr) : Bool :=
  a3 e.locals && a4 e.methods && a5 [] e.methods && a6 e.locals && e.noShadow [] [] &&
  a8 e.methods e.ifVars && groundFunnels e.locals

def WFProgram (d : Decls) (e : Expr) : Prop := wfDecls d = true /\ wfExpr e = true

end Funnelling.High
