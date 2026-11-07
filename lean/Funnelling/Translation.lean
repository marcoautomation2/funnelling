import Funnelling.High.Syntax
import Funnelling.Low.Syntax

namespace Funnelling

mutual
def trTy : High.Ty -> Low.Ty
  | .cls c ts => .cls c (trTys ts)
  | .var x => .var x
def trTys : List High.Ty -> List Low.Ty
  | [] => []
  | t :: ts => trTy t :: trTys ts
end

def trFunnel : High.Funnel -> Low.Funnel
  | .ground g => .ground (trTy g)
  | .funnel x => .funnel x

def trBounds (delta : High.Bounds) : Low.Bounds := delta.map fun p => (p.1, trTy p.2)

def trCtx (gamma : High.Ctx) : Low.Ctx := gamma.map fun p => (p.1, trTy p.2)

mutual
def trExpr : High.Expr -> Low.Expr
  | .var x => .var x
  | .call e ts m es => .call (trExpr e) (trTys ts) m (trExprs es)
  | .superCall e t ts m es => .superCall (trExpr e) (trTy t) (trTys ts) m (trExprs es)
  | .field e f => .field (trExpr e) f
  | .new c ts es => .new c (trTys ts) (trExprs es)
  | .newLocal c fs c' ts es ms =>
    .newLocal c (fs.map trFunnel) c' (trTys ts) (trExprs es) (trMethods ms)
  | .ifInst e0 t x e1 e2 => .ifInst (trExpr e0) (trTy t) x (trExpr e1) (trExpr e2)
def trExprs : List High.Expr -> List Low.Expr
  | [] => []
  | e :: es => trExpr e :: trExprs es
def trMethod : High.Method -> Low.Method
  | .mk delta t m ps e => .mk (trBounds delta) (trTy t) m (ps.map fun p => (trTy p.1, p.2)) (trExpr e)
def trMethods : List High.Method -> List Low.Method
  | [] => []
  | m :: ms => trMethod m :: trMethods ms
end

def trDec (dec : High.Dec) : Low.Dec :=
  { name := dec.name, bounds := trBounds dec.bounds, sup := dec.sup, supArgs := trTys dec.supArgs,
    methods := trMethods dec.methods, fields := dec.fields.map fun p => (trTy p.1, p.2) }

def trDecls (d : High.Decls) : Low.Decls := d.map trDec

end Funnelling
