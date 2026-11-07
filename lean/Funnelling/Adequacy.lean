import Funnelling.High.Reduction
import Funnelling.High.WellFormed
import Funnelling.Low.Soundness
import Funnelling.Translation

/-!
The formalization has two levels.
`Funnelling.High` follows the metarules of the paper as closely as possible; the appendix of the
paper compares it with the paper, rule by rule.
`Funnelling.Low` is free: its datatypes, functions and rules can change in any way that makes the
proofs easier (other binder representations, algorithmic typing, other judgements), and several
low levels can be tried.
The whole point is to keep the freedom of changing the low level without having to impact the
high level: a change of the low level changes only `Funnelling.Low`, the translation in
`Funnelling.Translation`, and the lemmas in this file, whose statements may change too.
What must not change is the high level and the theorems of `Funnelling.Soundness`, which state
the soundness of the paper and are proved through the lemmas in this file.
-/

namespace Funnelling

theorem isValue_tr {e : High.Expr} : (trExpr e).isValue = e.isValue := by
  sorry

theorem wfExpr_tr {d : High.Decls} {e : High.Expr} (hd : High.wfDecls d = true)
    (he : High.wfExpr e = true) : Low.wfExpr (trExpr e) = true := by
  sorry

theorem declsOk_tr {d : High.Decls} (hd : High.wfDecls d = true)
    (hok : forall dec, List.Mem dec d -> High.ClassOk d false dec) :
    Low.DeclsOk (trDecls d) := by
  sorry

theorem typing_tr {d : High.Decls} {e : High.Expr} {t : High.Ty} (hd : High.wfDecls d = true) :
    High.Typing d false [] [] e t <-> Low.Typing (trDecls d) false [] [] (trExpr e) (trTy t) := by
  sorry

theorem step_tr {d : High.Decls} {e e' : High.Expr} (hd : High.wfDecls d = true)
    (he : High.wfExpr e = true) (hs : High.Step d e e') :
    Low.Step (trDecls d) (trExpr e) (trExpr e') := by
  sorry

theorem step_back {d : High.Decls} {e : High.Expr} {e'' : Low.Expr} (hd : High.wfDecls d = true)
    (he : High.wfExpr e = true) (hs : Low.Step (trDecls d) (trExpr e) e'') :
    exists e', High.Step d e e' /\ trExpr e' = e'' := by
  sorry

end Funnelling
