import Funnelling.High.Syntax

namespace Funnelling.High

abbrev TSubst := List (Prod Name Ty)

def mkSubst (xs : List Name) (ts : List Ty) : Option TSubst :=
  if xs.length = ts.length then some (xs.zip ts) else none

def mkSubstF (fs : List Funnel) (ts : List Ty) : Option TSubst :=
  if fs.length = ts.length then
    some ((fs.zip ts).filterMap fun
      | (.funnel x, t) => some (x, t)
      | (.ground _, _) => none)
  else none

mutual
def Ty.subst (sigma : TSubst) : Ty -> Ty
  | .var x =>
    match sigma.lookup x with
    | some t => t
    | none => .var x
  | .cls c ts => .cls c (Ty.substList sigma ts)
def Ty.substList (sigma : TSubst) : List Ty -> List Ty
  | [] => []
  | t :: ts => t.subst sigma :: Ty.substList sigma ts
end

def Funnel.subst (sigma : TSubst) : Funnel -> Funnel
  | .ground g => .ground (g.subst sigma)
  | .funnel x =>
    match sigma.lookup x with
    | some t => .ground t
    | none => .funnel x

def Bounds.subst (sigma : TSubst) (delta : Bounds) : Bounds :=
  delta.map fun p => (p.1, p.2.subst sigma)

mutual
def Expr.tsubst (sigma : TSubst) : Expr -> Expr
  | .var x => .var x
  | .call e ts m es => .call (e.tsubst sigma) (Ty.substList sigma ts) m (Expr.tsubstList sigma es)
  | .superCall e t ts m es =>
    .superCall (e.tsubst sigma) (t.subst sigma) (Ty.substList sigma ts) m (Expr.tsubstList sigma es)
  | .field e f => .field (e.tsubst sigma) f
  | .new c ts es => .new c (Ty.substList sigma ts) (Expr.tsubstList sigma es)
  | .newLocal c fs c' ts es ms =>
    .newLocal c (fs.map (Funnel.subst sigma)) c' (Ty.substList sigma ts)
      (Expr.tsubstList sigma es) (Method.tsubstList sigma ms)
  | .ifInst e0 t x e1 e2 =>
    .ifInst (e0.tsubst sigma) (t.subst sigma) x (e1.tsubst sigma) (e2.tsubst sigma)
def Expr.tsubstList (sigma : TSubst) : List Expr -> List Expr
  | [] => []
  | e :: es => e.tsubst sigma :: Expr.tsubstList sigma es
def Method.tsubst (sigma : TSubst) : Method -> Method
  | .mk delta t m ps e =>
    .mk (Bounds.subst sigma delta) (t.subst sigma) m
      (ps.map fun p => (p.1.subst sigma, p.2)) (e.tsubst sigma)
def Method.tsubstList (sigma : TSubst) : List Method -> List Method
  | [] => []
  | m :: ms => m.tsubst sigma :: Method.tsubstList sigma ms
end

abbrev VSubst := List (Prod Name Expr)

mutual
def Expr.vsubst (sigma : VSubst) : Expr -> Expr
  | .var x =>
    match sigma.lookup x with
    | some v => v
    | none => .var x
  | .call e ts m es => .call (e.vsubst sigma) ts m (Expr.vsubstList sigma es)
  | .superCall e t ts m es => .superCall (e.vsubst sigma) t ts m (Expr.vsubstList sigma es)
  | .field e f => .field (e.vsubst sigma) f
  | .new c ts es => .new c ts (Expr.vsubstList sigma es)
  | .newLocal c fs c' ts es ms =>
    .newLocal c fs c' ts (Expr.vsubstList sigma es)
      (Method.vsubstList (sigma.filter fun p => p.1 != thisName) ms)
  | .ifInst e0 t x e1 e2 => .ifInst (e0.vsubst sigma) t x (e1.vsubst sigma) (e2.vsubst sigma)
def Expr.vsubstList (sigma : VSubst) : List Expr -> List Expr
  | [] => []
  | e :: es => e.vsubst sigma :: Expr.vsubstList sigma es
def Method.vsubst (sigma : VSubst) : Method -> Method
  | .mk delta t m ps e => .mk delta t m ps (e.vsubst sigma)
def Method.vsubstList (sigma : VSubst) : List Method -> List Method
  | [] => []
  | m :: ms => m.vsubst sigma :: Method.vsubstList sigma ms
end

abbrev Renaming := List (Prod Name Name)

def renameName (rho : Renaming) (x : Name) : Name :=
  match rho.lookup x with
  | some y => y
  | none => x

mutual
def Ty.rename (rho : Renaming) : Ty -> Ty
  | .var x => .var (renameName rho x)
  | .cls c ts => .cls c (Ty.renameList rho ts)
def Ty.renameList (rho : Renaming) : List Ty -> List Ty
  | [] => []
  | t :: ts => t.rename rho :: Ty.renameList rho ts
end

def Funnel.rename (rho : Renaming) : Funnel -> Funnel
  | .ground g => .ground g
  | .funnel x => .funnel (renameName rho x)

mutual
def Expr.freshen (rv rt : Renaming) : List Name -> Expr -> Option (Prod Expr (List Name))
  | ns, .var x => some (.var (renameName rv x), ns)
  | ns, .call e ts m es => do
    let (e', ns) <- e.freshen rv rt ns
    let (es', ns) <- Expr.freshenList rv rt ns es
    pure (.call e' (Ty.renameList rt ts) m es', ns)
  | ns, .superCall e t ts m es => do
    let (e', ns) <- e.freshen rv rt ns
    let (es', ns) <- Expr.freshenList rv rt ns es
    pure (.superCall e' (t.rename rt) (Ty.renameList rt ts) m es', ns)
  | ns, .field e f => do
    let (e', ns) <- e.freshen rv rt ns
    pure (.field e' f, ns)
  | ns, .new c ts es => do
    let (es', ns) <- Expr.freshenList rv rt ns es
    pure (.new c (Ty.renameList rt ts) es', ns)
  | ns, .newLocal c fs c' ts es ms => do
    let (es', ns) <- Expr.freshenList rv rt ns es
    let (ms', ns) <- Method.freshenList rv rt ns ms
    pure (.newLocal c (fs.map (Funnel.rename rt)) c' (Ty.renameList rt ts) es' ms', ns)
  | ns, .ifInst e0 t x e1 e2 => do
    let (e0', ns) <- e0.freshen rv rt ns
    match ns with
    | [] => none
    | y :: ns =>
      let (e1', ns) <- e1.freshen ((x, y) :: rv) rt ns
      let (e2', ns) <- e2.freshen rv rt ns
      pure (.ifInst e0' (t.rename rt) y e1' e2', ns)
def Expr.freshenList (rv rt : Renaming) : List Name -> List Expr -> Option (Prod (List Expr) (List Name))
  | ns, [] => some ([], ns)
  | ns, e :: es => do
    let (e', ns) <- e.freshen rv rt ns
    let (es', ns) <- Expr.freshenList rv rt ns es
    pure (e' :: es', ns)
def Method.freshen (rv rt : Renaming) : List Name -> Method -> Option (Prod Method (List Name))
  | ns, .mk delta t m ps e =>
    let tys := ns.take delta.length
    let xs := (ns.drop delta.length).take ps.length
    let rest := (ns.drop delta.length).drop ps.length
    if tys.length + xs.length < delta.length + ps.length then none
    else
      let rt' := (dom delta).zip tys ++ rt
      let rv' := (ps.map Prod.snd).zip xs ++ rv
      match e.freshen rv' rt' rest with
      | none => none
      | some (e', rest) =>
        some (.mk (delta.map fun p => (renameName rt' p.1, p.2.rename rt')) (t.rename rt') m
          ((ps.zip xs).map fun p => (p.1.1.rename rt', p.2)) e', rest)
def Method.freshenList (rv rt : Renaming) : List Name -> List Method -> Option (Prod (List Method) (List Name))
  | ns, [] => some ([], ns)
  | ns, m :: ms => do
    let (m', ns) <- m.freshen rv rt ns
    let (ms', ns) <- Method.freshenList rv rt ns ms
    pure (m' :: ms', ns)
end

end Funnelling.High
