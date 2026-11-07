import Funnelling.Low.Declarations
import Funnelling.Low.Typing

namespace Funnelling.Low

inductive ECtx where
  | hole
  | callRecv (ctx : ECtx) (gs : List Ty) (m : Name) (es : List Expr)
  | callArg (v : Expr) (gs : List Ty) (m : Name) (vs : List Expr) (ctx : ECtx) (es : List Expr)
  | superRecv (ctx : ECtx) (g : Ty) (gs : List Ty) (m : Name) (es : List Expr)
  | superArg (v : Expr) (g : Ty) (gs : List Ty) (m : Name) (vs : List Expr) (ctx : ECtx) (es : List Expr)
  | field (ctx : ECtx) (f : Name)
  | newArg (c : Name) (gs : List Ty) (vs : List Expr) (ctx : ECtx) (es : List Expr)
  | localArg (c : Name) (fs : List Funnel) (c' : Name) (gs : List Ty) (vs : List Expr) (ctx : ECtx)
      (es : List Expr) (ms : List Method)
  | ifCond (ctx : ECtx) (g : Ty) (x : Name) (e1 e2 : Expr)

def ECtx.plug : ECtx -> Expr -> Expr
  | .hole, e => e
  | .callRecv E gs m es, e => .call (E.plug e) gs m es
  | .callArg v gs m vs E es, e => .call v gs m (vs ++ E.plug e :: es)
  | .superRecv E g gs m es, e => .superCall (E.plug e) g gs m es
  | .superArg v g gs m vs E es, e => .superCall v g gs m (vs ++ E.plug e :: es)
  | .field E f, e => .field (E.plug e) f
  | .newArg c gs vs E es, e => .new c gs (vs ++ E.plug e :: es)
  | .localArg c fs c' gs vs E es ms, e => .newLocal c fs c' gs (vs ++ E.plug e :: es) ms
  | .ifCond E g x e1 e2, e => .ifInst (E.plug e) g x e1 e2

def ECtx.ok : ECtx -> Bool
  | .hole => true
  | .callRecv E gs _ _ => E.ok && Ty.allGround gs
  | .callArg v gs _ vs E _ => v.isValue && Ty.allGround gs && Expr.allValues vs && E.ok
  | .superRecv E g gs _ _ => E.ok && g.isGround && Ty.allGround gs
  | .superArg v g gs _ vs E _ => v.isValue && g.isGround && Ty.allGround gs && Expr.allValues vs && E.ok
  | .field E _ => E.ok
  | .newArg _ gs vs E _ => Ty.allGround gs && Expr.allValues vs && E.ok
  | .localArg _ fs _ gs vs E _ _ =>
    fs.all Funnel.isGround && Ty.allGround gs && Expr.allValues vs && E.ok
  | .ifCond E g _ _ _ => E.ok && g.isGround

def avoidNames (d : Decls) (e : Expr) : List Name := d.names ++ e.names

def fieldNames (dec : Dec) : List Name := dec.fields.map Prod.snd

inductive Step (d : Decls) : Expr -> Expr -> Prop
  | simpleFieldFound {c gs vs1 vs f v} {dec : Dec} :
      List.Mem dec d -> dec.name = c ->
      vs1.length = dec.fields.length ->
      (Expr.new c gs (vs1 ++ vs)).isValue = true ->
      ((fieldNames dec).zip vs1).lookup f = some v ->
      Step d (.field (.new c gs (vs1 ++ vs)) f) v
  | simpleFieldSuper {c gs vs1 vs f sigma} {dec : Dec} :
      List.Mem dec d -> dec.name = c ->
      vs1.length = dec.fields.length ->
      (Expr.new c gs (vs1 ++ vs)).isValue = true ->
      (fieldNames dec).contains f = false ->
      Not (c = objectName) ->
      mkSubst (dom dec.bounds) gs = some sigma ->
      Step d (.field (.new c gs (vs1 ++ vs)) f) (.field (.new dec.sup (Ty.substList sigma dec.supArgs) vs) f)
  | innerFieldSuper {c fs c' gs vs ms f} :
      (Expr.newLocal c fs c' gs vs ms).isValue = true ->
      Step d (.field (.newLocal c fs c' gs vs ms) f) (.field (.new c' gs vs) f)
  | ifThen {v c' ts ts' tv x e1 e1' e2} :
      v.isValue = true -> typeOf v = some tv ->
      Sub d [] tv (.cls c' ts') ->
      Fresh (avoidNames d (.ifInst v (.cls c' ts) x e1 e2)) e1 e1' ->
      Step d (.ifInst v (.cls c' ts) x e1 e2) (e1'.vsubst [(x, v)])
  | ifElse {v c' ts tv x e1 e2} :
      v.isValue = true -> typeOf v = some tv ->
      (forall ts', Not (Sub d [] tv (.cls c' ts'))) ->
      Step d (.ifInst v (.cls c' ts) x e1 e2) e2
  | simpleAddSuper {c gs vs0 gs' m vs} :
      (Expr.new c gs vs0).isValue = true -> Ty.allGround gs' = true -> Expr.allValues vs = true ->
      Step d (.call (.new c gs vs0) gs' m vs) (.superCall (.new c gs vs0) (.cls c gs) gs' m vs)
  | simpleFound {v0 c gs gs' m vs mt delta' t0 ps e0 sigma} {dec : Dec} :
      List.Mem dec d -> dec.name = c ->
      v0.isValue = true -> Ty.allGround gs = true -> Ty.allGround gs' = true -> Expr.allValues vs = true ->
      List.Mem mt dec.methods ->
      FreshM (avoidNames d (.superCall v0 (.cls c gs) gs' m vs)) mt (.mk delta' t0 m ps e0) ->
      mkSubst (dom dec.bounds ++ dom delta') (gs ++ gs') = some sigma ->
      ps.length = vs.length ->
      Step d (.superCall v0 (.cls c gs) gs' m vs)
        ((e0.tsubst sigma).vsubst ((thisName, v0) :: (ps.map Prod.snd).zip vs))
  | innerFound {c fs c' gs vs0 ms gs' m vs mt delta' t0 ps e0 sigma} :
      (Expr.newLocal c fs c' gs vs0 ms).isValue = true -> Ty.allGround gs' = true ->
      Expr.allValues vs = true ->
      List.Mem mt ms ->
      FreshM (avoidNames d (.call (.newLocal c fs c' gs vs0 ms) gs' m vs)) mt (.mk delta' t0 m ps e0) ->
      mkSubst (dom delta') gs' = some sigma ->
      ps.length = vs.length ->
      Step d (.call (.newLocal c fs c' gs vs0 ms) gs' m vs)
        ((e0.tsubst sigma).vsubst ((thisName, .newLocal c fs c' gs vs0 ms) :: (ps.map Prod.snd).zip vs))
  | innerSuper {c fs c' gs vs0 ms gs' m vs} :
      (Expr.newLocal c fs c' gs vs0 ms).isValue = true -> Ty.allGround gs' = true ->
      Expr.allValues vs = true ->
      (ms.map Method.name).contains m = false ->
      Step d (.call (.newLocal c fs c' gs vs0 ms) gs' m vs)
        (.superCall (.newLocal c fs c' gs vs0 ms) (.cls c' gs) gs' m vs)
  | searchSuper {v c gs gs' m vs sigma} {dec : Dec} :
      List.Mem dec d -> dec.name = c ->
      v.isValue = true -> Ty.allGround gs = true -> Ty.allGround gs' = true -> Expr.allValues vs = true ->
      (dec.methods.map Method.name).contains m = false ->
      Not (c = objectName) ->
      mkSubst (dom dec.bounds) gs = some sigma ->
      Step d (.superCall v (.cls c gs) gs' m vs)
        (.superCall v (.cls dec.sup (Ty.substList sigma dec.supArgs)) gs' m vs)
  | ctx {E : ECtx} {e e'} :
      E.ok = true -> Step d e e' -> Step d (E.plug e) (E.plug e')

inductive Steps (d : Decls) : Expr -> Expr -> Prop
  | refl {e} : Steps d e e
  | step {e e' e''} : Step d e e' -> Steps d e' e'' -> Steps d e e''

end Funnelling.Low
