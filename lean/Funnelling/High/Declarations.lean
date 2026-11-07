import Funnelling.High.Substitution

namespace Funnelling.High

def pairing (delta : Bounds) : List Funnel -> List Ty -> Option (Prod Bounds (List Ty))
  | [], [] => some ([], [])
  | .funnel x :: fs, t :: ts => do
    let b <- delta.lookup x
    let (delta', ts') <- pairing delta fs ts
    pure ((x, b) :: delta', t :: ts')
  | .ground g :: fs, t :: ts => if g.beq t then pairing delta fs ts else none
  | _, _ => none

mutual
def Expr.locals : Expr -> List K
  | .var _ => []
  | .call e _ _ es => e.locals ++ Expr.localsList es
  | .superCall e _ _ _ es => e.locals ++ Expr.localsList es
  | .field e _ => e.locals
  | .new _ _ es => Expr.localsList es
  | .newLocal c fs c' ts es ms => K.loc c fs c' ts es ms :: (Expr.localsList es ++ Method.localsList ms)
  | .ifInst e0 _ _ e1 e2 => e0.locals ++ e1.locals ++ e2.locals
def Expr.localsList : List Expr -> List K
  | [] => []
  | e :: es => e.locals ++ Expr.localsList es
def Method.locals : Method -> List K
  | .mk _ _ _ _ e => e.locals
def Method.localsList : List Method -> List K
  | [] => []
  | m :: ms => m.locals ++ Method.localsList ms
end

def declaredKs (d : Decls) : List K :=
  d.flatMap fun dec => K.top dec :: Method.localsList dec.methods

def Declared (d : Decls) (k : K) : Prop := List.Mem k (declaredKs d)

abbrev ScopeEntry := Prod Name (Prod Bounds (List Funnel))

mutual
def Expr.scopeEntries (env : Bounds) : Expr -> List ScopeEntry
  | .var _ => []
  | .call e _ _ es => e.scopeEntries env ++ Expr.scopeEntriesList env es
  | .superCall e _ _ _ es => e.scopeEntries env ++ Expr.scopeEntriesList env es
  | .field e _ => e.scopeEntries env
  | .new _ _ es => Expr.scopeEntriesList env es
  | .newLocal c fs _ _ es ms =>
    (c, (env, fs)) :: (Expr.scopeEntriesList env es ++
      match pairing env fs (fs.map Funnel.abs) with
      | some (inner, _) => Method.scopeEntriesList inner ms
      | none => [])
  | .ifInst e0 _ _ e1 e2 => e0.scopeEntries env ++ e1.scopeEntries env ++ e2.scopeEntries env
def Expr.scopeEntriesList (env : Bounds) : List Expr -> List ScopeEntry
  | [] => []
  | e :: es => e.scopeEntries env ++ Expr.scopeEntriesList env es
def Method.scopeEntries (env : Bounds) : Method -> List ScopeEntry
  | .mk delta _ _ _ e => e.scopeEntries (env ++ delta)
def Method.scopeEntriesList (env : Bounds) : List Method -> List ScopeEntry
  | [] => []
  | m :: ms => m.scopeEntries env ++ Method.scopeEntriesList env ms
end

def findDec (d : Decls) (c : Name) : Option Dec := d.find? fun dec => dec.name == c

def scope (d : Decls) (c : Name) (ts : List Ty) : Option (Prod Bounds (List Ty)) :=
  match findDec d c with
  | some dec => some (dec.bounds, ts)
  | none =>
    match (d.flatMap fun dec => Method.scopeEntriesList dec.bounds dec.methods).lookup c with
    | some (env, fs) => pairing env fs ts
    | none => none

def findK (d : Decls) (c : Name) : Option K := (declaredKs d).find? fun k => k.name == c

def generic (d : Decls) (c : Name) : Option (List Name) :=
  match findK d c with
  | some (.top dec) => some (dom dec.bounds)
  | some (.loc _ fs _ _ _ _) => some (domF fs)
  | none => none

def lookupMethod (ms : List Method) (m : Name) : Option Method := ms.find? fun mt => mt.name == m

def MethodIn (d : Decls) (mt : Method) (c : Name) : Prop :=
  exists k, Declared d k /\ k.name = c /\ List.Mem mt k.methods

def typeOf : Expr -> Option Ty
  | .new c gs _ => some (.cls c gs)
  | .newLocal c fs _ _ _ _ => some (.cls c (fs.map Funnel.abs))
  | _ => none

mutual
def Expr.isValue : Expr -> Bool
  | .new _ gs vs => Ty.allGround gs && Expr.allValues vs
  | .newLocal _ fs _ gs vs _ => fs.all Funnel.isGround && Ty.allGround gs && Expr.allValues vs
  | _ => false
def Expr.allValues : List Expr -> Bool
  | [] => true
  | e :: es => e.isValue && Expr.allValues es
end

def Bounds.names (delta : Bounds) : List Name :=
  delta.flatMap fun p => p.1 :: p.2.ftv

mutual
def Expr.names : Expr -> List Name
  | .var x => [x]
  | .call e ts _ es => e.names ++ Ty.ftvList ts ++ Expr.namesList es
  | .superCall e t ts _ es => e.names ++ t.ftv ++ Ty.ftvList ts ++ Expr.namesList es
  | .field e _ => e.names
  | .new _ ts es => Ty.ftvList ts ++ Expr.namesList es
  | .newLocal _ fs _ ts es ms =>
    domF fs ++ Ty.ftvList ts ++ Expr.namesList es ++ Method.namesList ms
  | .ifInst e0 t x e1 e2 => x :: e0.names ++ t.ftv ++ e1.names ++ e2.names
def Expr.namesList : List Expr -> List Name
  | [] => []
  | e :: es => e.names ++ Expr.namesList es
def Method.names : Method -> List Name
  | .mk delta t _ ps e =>
    Bounds.names delta ++ t.ftv ++ ps.flatMap (fun p => p.2 :: p.1.ftv) ++ e.names
def Method.namesList : List Method -> List Name
  | [] => []
  | m :: ms => m.names ++ Method.namesList ms
end

def Decls.names (d : Decls) : List Name :=
  d.flatMap fun dec =>
    Bounds.names dec.bounds ++ Ty.ftvList dec.supArgs ++ Method.namesList dec.methods ++
      dec.fields.flatMap fun p => p.1.ftv

def freshNames (avoid ns : List Name) : Bool :=
  decide ns.Nodup && ns.all fun n => !(avoid.contains n)

def Fresh (avoid : List Name) (e e' : Expr) : Prop :=
  exists ns, Expr.freshen [] [] ns e = some (e', []) /\ freshNames avoid ns = true

def FreshM (avoid : List Name) (mt mt' : Method) : Prop :=
  exists ns, Method.freshen [] [] ns mt = some (mt', []) /\ freshNames avoid ns = true

end Funnelling.High
