/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.ConePullbackLimit
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-! Import-only clients for native cones, nonidentity arrows, and the empty index. -/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v

namespace SheafCohomologyExamples.ConePullbackLimitClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

/-- The public component coherence exported by the producer is available
through an ordinary import, for three composable actual base arrows. -/
private theorem type_pullbackCompInv_assoc {W X Y Z : TopCat.{v}}
    (r : W ⟶ X) (q : X ⟶ Y) (g : Y ⟶ Z) (F : Z.Sheaf (Type v)) :
    TopCat.Sheaf.pullbackCompInv (Type v) r (q ≫ g) F ≫
        (TopCat.Sheaf.pullback (Type v) r).map
          (TopCat.Sheaf.pullbackCompInv (Type v) q g F) =
      TopCat.Sheaf.pullbackCompInv (Type v) (r ≫ q) g F ≫
        TopCat.Sheaf.pullbackCompInv (Type v) r q
          ((TopCat.Sheaf.pullback (Type v) g).obj F) :=
  SheafedSpace.pullbackCompInv_assoc (Type v) r q g F

private theorem type_first_arrow (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) : C.π.app (op (1 : Fin 3)) ≫ S.map first.op =
      C.π.app (op (0 : Fin 3)) := C.w first.op

private theorem type_second_arrow (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) : C.π.app (op (2 : Fin 3)) ≫ S.map second.op =
      C.π.app (op (1 : Fin 3)) := C.w second.op

/-- The criterion accepts the actual projection mates of a Type-valued cone. -/
private noncomputable def typeCriterion (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) (hc : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hK : IsColimit (SheafedSpace.conePullbackCocone (Type v) S C)) : IsLimit C :=
  SheafedSpace.isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone
    (Type v) S C hc hK

private theorem type_first_projection (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C Q : Cone S) (hc : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hK : IsColimit (SheafedSpace.conePullbackCocone (Type v) S C)) :
    SheafedSpace.conePullbackLimitLift (Type v) S C hc hK Q ≫
      C.π.app (op (0 : Fin 3)) = Q.π.app (op (0 : Fin 3)) :=
  (typeCriterion S C hc hK).fac Q (op (0 : Fin 3))

private theorem type_second_projection (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C Q : Cone S) (hc : IsLimit ((SheafedSpace.forget (Type v)).mapCone C))
    (hK : IsColimit (SheafedSpace.conePullbackCocone (Type v) S C)) :
    SheafedSpace.conePullbackLimitLift (Type v) S C hc hK Q ≫
      C.π.app (op (2 : Fin 3)) = Q.π.app (op (2 : Fin 3)) :=
  (typeCriterion S C hc hK).fac Q (op (2 : Fin 3))

private theorem type_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (C : Cone S) : C.π.app (op (2 : Fin 3)) ≫ S.map (first ≫ second).op =
      C.π.app (op (0 : Fin 3)) := C.w (first ≫ second).op

/-- Type-valued reconstruction using only a genuine space limit and sheaf colimit. -/
private noncomputable def typeReconstruction (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v)))
    (K : Cocone (SheafedSpace.conePullback (Type v) S c))
    (hc : IsLimit c) (hK : IsColimit K) :
    IsLimit (SheafedSpace.coneOfPullbackCocone (Type v) S c K) :=
  SheafedSpace.coneOfPullbackCoconeIsLimit (Type v) S c K hc hK

/-- Additive coefficients exercise the same genuine native criterion. -/
private noncomputable def additiveCriterion (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) (hc : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hK : IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :
    IsLimit C :=
  SheafedSpace.isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone
    AddCommGrpCat.{v} S C hc hK

private theorem additive_first_arrow (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) : C.π.app (op (1 : Fin 3)) ≫ S.map first.op =
      C.π.app (op (0 : Fin 3)) := C.w first.op

private theorem additive_second_arrow (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C : Cone S) : C.π.app (op (2 : Fin 3)) ≫ S.map second.op =
      C.π.app (op (1 : Fin 3)) := C.w second.op

private theorem additive_mate (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C Q : Cone S)
    (hc : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hK : IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :
    SheafedSpace.sheafMate AddCommGrpCat.{v}
      (SheafedSpace.conePullbackLimitLift AddCommGrpCat.{v} S C hc hK Q) =
        SheafedSpace.conePullbackLimitSheafMap AddCommGrpCat.{v} S C hc hK Q :=
  SheafedSpace.conePullbackLimitLift_mate AddCommGrpCat.{v} S C hc hK Q

private theorem additive_composite (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (C Q : Cone S)
    (hc : IsLimit ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone C))
    (hK : IsColimit (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S C)) :
    SheafedSpace.conePullbackLimitLift AddCommGrpCat.{v} S C hc hK Q ≫
      C.π.app (op (2 : Fin 3)) ≫ S.map (first ≫ second).op =
        Q.π.app (op (0 : Fin 3)) := by
  rw [C.w (first ≫ second).op]
  exact (additiveCriterion S C hc hK).fac Q (op (0 : Fin 3))

private noncomputable def additiveReconstruction (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    (K : Cocone (SheafedSpace.conePullback AddCommGrpCat.{v} S c))
    (hc : IsLimit c) (hK : IsColimit K) :
    IsLimit (SheafedSpace.coneOfPullbackCocone AddCommGrpCat.{v} S c K) :=
  SheafedSpace.coneOfPullbackCoconeIsLimit AddCommGrpCat.{v} S c K hc hK

private def emptyDiagram : PEmptyᵒᵖ ⥤ SheafedSpace (Type 0) where
  obj := fun i ↦ nomatch i
  map := fun {i} ↦ nomatch i

private def emptySpaceCone :
    Cone (emptyDiagram ⋙ SheafedSpace.forget (Type 0)) where
  pt := TopCat.of PUnit.{1}
  π := {
    app := fun i ↦ nomatch i
    naturality := by
      intro i
      exact nomatch i }

private noncomputable def emptySpaceIsLimit : IsLimit emptySpaceCone where
  lift := fun Q ↦ TopCat.isTerminalPUnit.from Q.pt
  fac := by
    intro Q i
    exact nomatch i
  uniq := by
    intro Q m hm
    exact TopCat.isTerminalPUnit.hom_ext _ _

private def emptySheafCocone (F : emptySpaceCone.pt.Sheaf (Type 0)) :
    Cocone (SheafedSpace.conePullback (Type 0) emptyDiagram emptySpaceCone) where
  pt := F
  ι := {
    app := fun i ↦ nomatch i
    naturality := by
      intro i
      exact nomatch i }

private noncomputable def emptyNativeOfInitial (F : emptySpaceCone.pt.Sheaf (Type 0))
    (hF : IsColimit (emptySheafCocone F)) :
    IsLimit (SheafedSpace.coneOfPullbackCocone (Type 0)
      emptyDiagram emptySpaceCone (emptySheafCocone F)) :=
  SheafedSpace.coneOfPullbackCoconeIsLimit (Type 0)
    emptyDiagram emptySpaceCone (emptySheafCocone F) emptySpaceIsLimit hF

end SheafCohomologyExamples.ConePullbackLimitClient
