namespace Funnelling.Low

abbrev Name := String

inductive Ty where
  | cls (c : Name) (args : List Ty)
  | var (x : Name)
  deriving Repr

inductive Funnel where
  | ground (g : Ty)
  | funnel (x : Name)
  deriving Repr

abbrev Bounds := List (Prod Name Ty)

mutual
inductive Expr where
  | var (x : Name)
  | call (recv : Expr) (targs : List Ty) (m : Name) (args : List Expr)
  | superCall (recv : Expr) (start : Ty) (targs : List Ty) (m : Name) (args : List Expr)
  | field (recv : Expr) (f : Name)
  | new (c : Name) (targs : List Ty) (args : List Expr)
  | newLocal (c : Name) (fs : List Funnel) (sup : Name) (supArgs : List Ty)
      (args : List Expr) (ms : List Method)
  | ifInst (e0 : Expr) (t : Ty) (x : Name) (e1 e2 : Expr)
  deriving Repr
inductive Method where
  | mk (bounds : Bounds) (ret : Ty) (m : Name) (params : List (Prod Ty Name)) (body : Expr)
  deriving Repr
end

structure Dec where
  name : Name
  bounds : Bounds
  sup : Name
  supArgs : List Ty
  methods : List Method
  fields : List (Prod Ty Name)
  deriving Repr

inductive K where
  | top (dec : Dec)
  | loc (c : Name) (fs : List Funnel) (sup : Name) (supArgs : List Ty)
      (args : List Expr) (ms : List Method)
  deriving Repr

abbrev Decls := List Dec

abbrev Ctx := List (Prod Name Ty)

def objectName : Name := "Object"

def thisName : Name := "this"

def Method.name : Method -> Name
  | .mk _ _ m _ _ => m

def Method.bounds : Method -> Bounds
  | .mk delta _ _ _ _ => delta

def Method.body : Method -> Expr
  | .mk _ _ _ _ e => e

def K.name : K -> Name
  | .top dec => dec.name
  | .loc c _ _ _ _ _ => c

def K.methods : K -> List Method
  | .top dec => dec.methods
  | .loc _ _ _ _ _ ms => ms

def dom (delta : Bounds) : List Name := delta.map Prod.fst

def cod (delta : Bounds) : List Ty := delta.map Prod.snd

def Funnel.abs : Funnel -> Ty
  | .ground g => g
  | .funnel x => .var x

def domF (fs : List Funnel) : List Name :=
  fs.filterMap fun
    | .funnel x => some x
    | .ground _ => none

def vars (xs : List Name) : List Ty := xs.map Ty.var

mutual
def Ty.isGround : Ty -> Bool
  | .var _ => false
  | .cls _ ts => Ty.allGround ts
def Ty.allGround : List Ty -> Bool
  | [] => true
  | t :: ts => t.isGround && Ty.allGround ts
end

mutual
def Ty.ftv : Ty -> List Name
  | .var x => [x]
  | .cls _ ts => Ty.ftvList ts
def Ty.ftvList : List Ty -> List Name
  | [] => []
  | t :: ts => t.ftv ++ Ty.ftvList ts
end

mutual
def Ty.beq : Ty -> Ty -> Bool
  | .var x, .var y => x == y
  | .cls c ts, .cls c' ts' => c == c' && Ty.beqList ts ts'
  | _, _ => false
def Ty.beqList : List Ty -> List Ty -> Bool
  | [], [] => true
  | t :: ts, t' :: ts' => Ty.beq t t' && Ty.beqList ts ts'
  | _, _ => false
end

def Funnel.isGround : Funnel -> Bool
  | .ground g => g.isGround
  | .funnel _ => false

end Funnelling.Low
