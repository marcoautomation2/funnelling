import Funnelling.Adequacy

namespace Funnelling.High

def DeclsOk (d : Decls) : Prop := wfDecls d = true /\ forall dec, List.Mem dec d -> ClassOk d false dec

theorem stepWellFormed {d e e' t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) (hs : Step d e e') : wfExpr e' = true := by
  sorry

theorem progress {d e t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) :
    e.isValue = true \/ exists e', Step d e e' := by
  match Low.progress (declsOk_tr hd.1 hd.2) (wfExpr_tr hd.1 he) ((typing_tr hd.1).mp ht) with
  | Or.inl hv => exact Or.inl (isValue_tr.symm.trans hv)
  | Or.inr (Exists.intro _ hs) =>
    match step_back hd.1 he hs with
    | Exists.intro e' (And.intro h _) => exact Or.inr (Exists.intro e' h)

theorem preservation {d e e' t} (hd : DeclsOk d) (he : wfExpr e = true)
    (ht : Typing d false [] [] e t) (hs : Step d e e') : Typing d false [] [] e' t :=
  (typing_tr hd.1).mpr
    (Low.preservation (declsOk_tr hd.1 hd.2) (wfExpr_tr hd.1 he) ((typing_tr hd.1).mp ht)
      (step_tr hd.1 he hs))

theorem typeSoundness {d e0 e t} (hd : DeclsOk d) (he0 : wfExpr e0 = true)
    (ht : Typing d false [] [] e0 t) (hs : Steps d e0 e) :
    Typing d false [] [] e t /\ (e.isValue = true \/ exists e', Step d e e') := by
  induction hs with
  | refl => exact And.intro ht (progress hd he0 ht)
  | step h1 _ ih => exact ih (stepWellFormed hd he0 ht h1) (preservation hd he0 ht h1)

end Funnelling.High
