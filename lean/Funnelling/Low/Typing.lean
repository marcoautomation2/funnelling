import Funnelling.Low.Declarations

namespace Funnelling.Low

inductive Sub (d : Decls) (delta : Bounds) : Ty -> Ty -> Prop
  | refl {t} : Sub d delta t t
  | inherit {c ts0 t' sigma} {dec : Dec} :
      List.Mem dec d -> dec.name = c ->
      mkSubst (dom dec.bounds) ts0 = some sigma ->
      Sub d delta ((Ty.cls dec.sup dec.supArgs).subst sigma) t' ->
      Sub d delta (.cls c ts0) t'
  | inheritLocal {c fs c' ts' es ms ts t' sigma} :
      Declared d (.loc c fs c' ts' es ms) ->
      mkSubstF fs ts = some sigma ->
      Sub d delta ((Ty.cls c' ts').subst sigma) t' ->
      Sub d delta (.cls c ts) t'
  | var {x t t'} :
      delta.lookup x = some t -> Sub d delta t t' -> Sub d delta (.var x) t'

inductive Kind (d : Decls) (delta : Bounds) : Ty -> Prop
  | var {x} : (delta.lookup x).isSome = true -> Kind d delta (.var x)
  | cls {c ts delta0 ts0 sigma} :
      scope d c ts = some (delta0, ts0) ->
      (forall t, List.Mem t ts -> Kind d delta t) ->
      mkSubst (dom delta0) ts0 = some sigma ->
      (forall p, List.Mem p (ts0.zip (Ty.substList sigma (cod delta0))) -> Sub d delta p.1 p.2) ->
      Kind d delta (.cls c ts)

inductive Cast (d : Decls) (delta : Bounds) : Ty -> Ty -> Prop
  | up {t t'} : Sub d delta t t' -> Cast d delta t t'
  | var {x t t'} : delta.lookup x = some t -> Cast d delta t t' -> Cast d delta (.var x) t'
  | down {c ts c' ts0 xs ts'} :
      Sub d delta (.cls c ts) (.cls c' ts0) ->
      generic d c = some xs ->
      Sub d [] (.cls c (vars xs)) (.cls c' ts') ->
      (forall x, List.Mem x xs -> List.Mem x (Ty.ftvList ts')) ->
      Cast d delta (.cls c' ts0) (.cls c ts)

def OverrideOk1 (d : Decls) (t : Ty) (mt : Method) : Prop :=
  match t, mt with
  | .cls c ts, .mk delta' t0' m ps' _ =>
    (exists dec : Dec, List.Mem dec d /\ dec.name = c /\ Not (List.Mem m (dec.methods.map Method.name)))
    \/ (exists (dec : Dec) (delta'' : Bounds) (t0 : Ty) (ps : List (Prod Ty Name)) (e : Expr) (sigma : TSubst), List.Mem dec d /\ dec.name = c /\
          List.Mem (Method.mk delta'' t0 m ps e) dec.methods /\
          mkSubst (dom dec.bounds ++ dom delta'') (ts ++ vars (dom delta')) = some sigma /\
          Ty.substList sigma (cod delta'') = cod delta' /\
          Ty.substList sigma (t0 :: ps.map Prod.fst) = t0' :: ps'.map Prod.fst)
    \/ (exists fs c0 ts0 es ms delta'' t0 ps e sigmaF sigma,
          Declared d (.loc c fs c0 ts0 es ms) /\
          List.Mem (Method.mk delta'' t0 m ps e) ms /\
          mkSubstF fs ts = some sigmaF /\
          mkSubst (dom delta'') (vars (dom delta')) = some sigma /\
          Ty.substList (sigmaF ++ sigma) (cod delta'') = cod delta' /\
          Ty.substList (sigmaF ++ sigma) (t0 :: ps.map Prod.fst) = t0' :: ps'.map Prod.fst)
  | .var _, _ => False

def OverrideOk (d : Decls) (delta : Bounds) (t : Ty) (ms : List Method) : Prop :=
  forall mt c ts, List.Mem mt ms -> Sub d delta t (.cls c ts) -> OverrideOk1 d (.cls c ts) mt

def Consistent (d : Decls) : K -> Prop
  | .loc c fs c0 ts _ ms =>
    exists fs' ts' es' ms' sigma,
      Declared d (.loc c fs' c0 ts' es' ms') /\
      mkSubstF fs' (fs.map Funnel.abs) = some sigma /\
      ts = Ty.substList sigma ts' /\
      (forall m, List.Mem m (ms'.map Method.name) <-> List.Mem m (ms.map Method.name)) /\
      forall mt, List.Mem mt ms -> OverrideOk1 d (.cls c (fs.map Funnel.abs)) mt
  | .top _ => False

def restrict (gamma : Ctx) (xs : List Name) : Ctx :=
  gamma.filter fun p => p.1 != thisName && p.2.ftv.all fun x => xs.contains x

def withoutThis (gamma : Ctx) : Ctx := gamma.filter fun p => p.1 != thisName

mutual
inductive Typing (d : Decls) (java : Bool) : Bounds -> Ctx -> Expr -> Ty -> Prop
  | subs {delta gamma e t1 t2} :
      Typing d java delta gamma e t1 -> Kind d delta t2 -> Sub d delta t1 t2 ->
      Typing d java delta gamma e t2
  | var {delta gamma x t} :
      gamma.lookup x = some t -> Typing d java delta gamma (.var x) t
  | newObject {delta gamma} :
      Typing d java delta gamma (.new objectName [] []) (.cls objectName [])
  | declField {delta gamma e c ts' t f sigma} {dec : Dec} :
      Typing d java delta gamma e (.cls c ts') ->
      List.Mem dec d -> dec.name = c ->
      List.Mem (t, f) dec.fields ->
      mkSubst (dom dec.bounds) ts' = some sigma ->
      Typing d java delta gamma (.field e f) (t.subst sigma)
  | call {delta gamma e0 c0 ts0 delta0 ts2 delta1 t0 m ps body ts1 es sigma} :
      Typing d java delta gamma e0 (.cls c0 ts0) ->
      scope d c0 ts0 = some (delta0, ts2) ->
      MethodIn d (.mk delta1 t0 m ps body) c0 ->
      mkSubst (dom delta0 ++ dom delta1) (ts2 ++ ts1) = some sigma ->
      (forall t, List.Mem t ts1 -> Kind d delta t) ->
      (forall p, List.Mem p (ts1.zip (Ty.substList sigma (cod delta1))) -> Sub d delta p.1 p.2) ->
      es.length = ps.length ->
      (forall p, List.Mem p (es.zip (Ty.substList sigma (ps.map Prod.fst))) ->
        Typing d java delta gamma p.1 p.2) ->
      Typing d java delta gamma (.call e0 ts1 m es) (t0.subst sigma)
  | superCall {delta gamma e0 c ts c0 ts0 delta1 t0 m ps body ts1 es sigma} {dec0 dec : Dec} :
      Sub d delta (.cls c ts) (.cls c0 ts0) ->
      List.Mem dec0 d -> dec0.name = c0 ->
      MethodIn d (.mk delta1 t0 m ps body) c0 ->
      mkSubst (dom dec0.bounds ++ dom delta1) (ts0 ++ ts1) = some sigma ->
      List.Mem dec d -> dec.name = c ->
      Kind d delta (.cls c ts) ->
      (forall t, List.Mem t ts1 -> Kind d delta t) ->
      (forall p, List.Mem p (ts1.zip (Ty.substList sigma (cod delta1))) -> Sub d delta p.1 p.2) ->
      Typing d java delta gamma e0 (.cls c ts) ->
      es.length = ps.length ->
      (forall p, List.Mem p (es.zip (Ty.substList sigma (ps.map Prod.fst))) ->
        Typing d java delta gamma p.1 p.2) ->
      Typing d java delta gamma (.superCall e0 (.cls c ts) ts1 m es) (t0.subst sigma)
  | newTop {delta gamma c ts' es1 es2 sigma t''} {dec : Dec} :
      List.Mem dec d -> dec.name = c ->
      Kind d delta (.cls c ts') ->
      mkSubst (dom dec.bounds) ts' = some sigma ->
      es1.length = dec.fields.length ->
      (forall p, List.Mem p (es1.zip (Ty.substList sigma (dec.fields.map Prod.fst))) ->
        Typing d java delta gamma p.1 p.2) ->
      Typing d java delta gamma (.new dec.sup (Ty.substList sigma dec.supArgs) es2) t'' ->
      Typing d java delta gamma (.new c ts' (es1 ++ es2)) (.cls c ts')
  | newLocal {delta gamma c fs c0 ts es ms delta' ts'' t''} :
      java = false ->
      Consistent d (.loc c fs c0 ts es ms) ->
      pairing delta fs (fs.map Funnel.abs) = some (delta', ts'') ->
      (forall x, List.Mem x (Ty.ftvList (cod delta')) -> List.Mem x (dom delta')) ->
      Kind d delta' (.cls c (fs.map Funnel.abs)) ->
      Kind d delta' (.cls c0 ts) ->
      Typing d java delta gamma (.new c0 ts es) t'' ->
      (forall mt, List.Mem mt ms ->
        MethodOk d java delta'
          (restrict gamma (Ty.ftvList (fs.map Funnel.abs)) ++ [(thisName, .cls c (fs.map Funnel.abs))]) mt) ->
      OverrideOk d delta' (.cls c0 ts) ms ->
      Typing d java delta gamma (.newLocal c fs c0 ts es ms) (.cls c (fs.map Funnel.abs))
  | newLocalJava {delta gamma c c0 ts es ms t''} :
      java = true ->
      Kind d delta (.cls c0 ts) ->
      Typing d java delta gamma (.new c0 ts es) t'' ->
      (forall mt, List.Mem mt ms ->
        MethodOk d java delta (withoutThis gamma ++ [(thisName, .cls c [])]) mt) ->
      OverrideOk d delta (.cls c0 ts) ms ->
      Typing d java delta gamma (.newLocal c [] c0 ts es ms) (.cls c [])
  | ifInst {delta gamma e0 t0 t x e1 e2 t'} :
      Typing d java delta gamma e0 t0 -> Kind d delta t -> Cast d delta t0 t ->
      Typing d java delta (gamma ++ [(x, t)]) e1 t' -> Typing d java delta gamma e2 t' ->
      Typing d java delta gamma (.ifInst e0 t x e1 e2) t'
inductive MethodOk (d : Decls) (java : Bool) : Bounds -> Ctx -> Method -> Prop
  | mk {delta gamma delta' t0 m ps e} :
      (forall t, List.Mem t (cod delta') -> Kind d (delta ++ delta') t) ->
      (forall t, List.Mem t (t0 :: ps.map Prod.fst) -> Kind d (delta ++ delta') t) ->
      Typing d java (delta ++ delta') (gamma ++ ps.map fun p => (p.2, p.1)) e t0 ->
      MethodOk d java delta gamma (.mk delta' t0 m ps e)
end

def ClassOk (d : Decls) (java : Bool) (dec : Dec) : Prop :=
  (forall t, List.Mem t (cod dec.bounds) -> Kind d dec.bounds t) /\
  (forall t, List.Mem t (Ty.cls dec.sup dec.supArgs :: dec.fields.map Prod.fst) -> Kind d dec.bounds t) /\
  (forall mt, List.Mem mt dec.methods ->
    MethodOk d java dec.bounds [(thisName, .cls dec.name (vars (dom dec.bounds)))] mt) /\
  OverrideOk d dec.bounds (.cls dec.sup dec.supArgs) dec.methods

def ProgOk (d : Decls) (java : Bool) (e : Expr) : Prop :=
  (forall dec, List.Mem dec d -> ClassOk d java dec) /\ exists t, Typing d java [] [] e t

end Funnelling.Low
