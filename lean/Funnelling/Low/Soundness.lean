import Funnelling.Low.Reduction
import Funnelling.Low.WellFormed

namespace Funnelling.Low

def DeclsOk (d : Decls) : Prop := wfDecls d = true /\ forall dec, List.Mem dec d -> ClassOk d false dec

theorem progress {d e t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) :
    e.isValue = true \/ exists e', Step d e e' := by
  sorry

theorem preservation {d e e' t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) (hs : Step d e e') : Typing d false [] [] e' t := by
  sorry

end Funnelling.Low
