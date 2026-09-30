/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.LimitConstruction
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Topology.Category.TopCat.Limits.Basic


/-! Import-only checks of actual native limits over finite and empty diagrams. -/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v

namespace SheafCohomologyExamples.LimitConstructionClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

private noncomputable def typeFiniteCone
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c) : LimitCone S :=
  SheafedSpace.limitConeOfSpaceCone (Type v) S c hc

private theorem typeFinite_forget
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c) :
    (SheafedSpace.forget (Type v)).mapCone (typeFiniteCone S c hc).cone = c :=
  SheafedSpace.limitConeOfSpaceCone_forget (Type v) S c hc

private theorem typeFinite_first
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c) :
    (typeFiniteCone S c hc).cone.π.app (op (1 : Fin 3)) ≫ S.map first.op =
      (typeFiniteCone S c hc).cone.π.app (op (0 : Fin 3)) :=
  (typeFiniteCone S c hc).cone.w first.op

private theorem typeFinite_second
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c) :
    (typeFiniteCone S c hc).cone.π.app (op (2 : Fin 3)) ≫ S.map second.op =
      (typeFiniteCone S c hc).cone.π.app (op (1 : Fin 3)) :=
  (typeFiniteCone S c hc).cone.w second.op

private theorem typeFinite_composite
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c) :
    (typeFiniteCone S c hc).cone.π.app (op (2 : Fin 3)) ≫
        S.map (first ≫ second).op =
      (typeFiniteCone S c hc).cone.π.app (op (0 : Fin 3)) :=
  (typeFiniteCone S c hc).cone.w (first ≫ second).op

private theorem typeFinite_mate
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (i : Fin 3) :
    SheafedSpace.sheafMate (Type v) ((typeFiniteCone S c hc).cone.π.app (op i)) =
      (SheafedSpace.conePullbackColimitCocone (Type v) S c).ι.app i :=
  SheafedSpace.limitConeOfSpaceCone_π_mate (Type v) S c hc (op i)

private theorem typeFinite_mate_colimit_ι
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (S ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (i : Fin 3) :
    SheafedSpace.sheafMate (Type v) ((typeFiniteCone S c hc).cone.π.app (op i)) =
      (by letI : HasColimitsOfShape (Fin 3) (c.pt.Sheaf (Type v)) :=
            CategoryTheory.Sheaf.instHasColimitsOfShape
          exact colimit.ι (SheafedSpace.conePullback (Type v) S c) i) :=
  SheafedSpace.limitConeOfSpaceCone_π_mate_colimit_ι (Type v) S c hc i

private theorem typeFinite_hasLimit
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} (Type v)) : HasLimit S :=
  SheafedSpace.hasLimitOfHasLimitForget (Type v) S

private noncomputable def additiveFiniteCone
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v}))
    (hc : IsLimit c) : LimitCone S :=
  SheafedSpace.limitConeOfSpaceCone AddCommGrpCat.{v} S c hc

private theorem additiveFinite_first
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (hc : IsLimit c) :
    (additiveFiniteCone S c hc).cone.π.app (op (1 : Fin 3)) ≫ S.map first.op =
      (additiveFiniteCone S c hc).cone.π.app (op (0 : Fin 3)) :=
  (additiveFiniteCone S c hc).cone.w first.op

private theorem additiveFinite_second
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (hc : IsLimit c) :
    (additiveFiniteCone S c hc).cone.π.app (op (2 : Fin 3)) ≫ S.map second.op =
      (additiveFiniteCone S c hc).cone.π.app (op (1 : Fin 3)) :=
  (additiveFiniteCone S c hc).cone.w second.op

private theorem additiveFinite_composite
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (hc : IsLimit c) :
    (additiveFiniteCone S c hc).cone.π.app (op (2 : Fin 3)) ≫
        S.map (first ≫ second).op =
      (additiveFiniteCone S c hc).cone.π.app (op (0 : Fin 3)) :=
  (additiveFiniteCone S c hc).cone.w (first ≫ second).op

private theorem additiveFinite_mate
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (hc : IsLimit c)
    (i : Fin 3) :
    SheafedSpace.sheafMate AddCommGrpCat.{v}
        ((additiveFiniteCone S c hc).cone.π.app (op i)) =
      (SheafedSpace.conePullbackColimitCocone AddCommGrpCat.{v} S c).ι.app i :=
  SheafedSpace.limitConeOfSpaceCone_π_mate AddCommGrpCat.{v} S c hc (op i)

private theorem additiveFinite_mate_colimit_ι
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v})
    (c : Cone (S ⋙ SheafedSpace.forget AddCommGrpCat.{v})) (hc : IsLimit c)
    (i : Fin 3) :
    SheafedSpace.sheafMate AddCommGrpCat.{v}
        ((additiveFiniteCone S c hc).cone.π.app (op i)) =
      (by letI : HasColimitsOfShape (Fin 3) (c.pt.Sheaf AddCommGrpCat.{v}) :=
            CategoryTheory.Sheaf.instHasColimitsOfShape
          exact colimit.ι (SheafedSpace.conePullback AddCommGrpCat.{v} S c) i) :=
  SheafedSpace.limitConeOfSpaceCone_π_mate_colimit_ι AddCommGrpCat.{v} S c hc i

private theorem additiveFinite_hasLimit
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace.{v+1,v,v} AddCommGrpCat.{v}) : HasLimit S :=
  SheafedSpace.hasLimitOfHasLimitForget AddCommGrpCat.{v} S

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

private noncomputable def emptyNativeLimitCone : LimitCone emptyDiagram :=
  SheafedSpace.limitConeOfSpaceCone (Type 0) emptyDiagram
    emptySpaceCone emptySpaceIsLimit

private theorem emptyNative_carrier :
    (emptyNativeLimitCone.cone.pt : TopCat) = TopCat.of PUnit.{1} :=
  SheafedSpace.limitConeOfSpaceCone_carrier (Type 0) emptyDiagram
    emptySpaceCone emptySpaceIsLimit

private theorem emptyNative_sheaf :
    emptyNativeLimitCone.cone.pt.sheaf =
      (SheafedSpace.conePullbackColimitCocone (Type 0)
        emptyDiagram emptySpaceCone).pt :=
  SheafedSpace.limitConeOfSpaceCone_sheaf (Type 0) emptyDiagram
    emptySpaceCone emptySpaceIsLimit

private noncomputable def emptyNative_sheafIsColimit :
    IsColimit (SheafedSpace.conePullbackColimitCocone (Type 0)
      emptyDiagram emptySpaceCone) :=
  SheafedSpace.conePullbackColimitCocone_isColimit (Type 0)
    emptyDiagram emptySpaceCone

private noncomputable def emptyNative_initialSheaf :
    IsInitial (SheafedSpace.conePullbackColimitCocone (Type 0)
      emptyDiagram emptySpaceCone).pt := by
  let K := SheafedSpace.conePullbackColimitCocone (Type 0)
    emptyDiagram emptySpaceCone
  have hK : IsColimit K := emptyNative_sheafIsColimit
  letI (Y : emptySpaceCone.pt.Sheaf (Type 0)) : Unique (K.pt ⟶ Y) := {
    default := hK.desc {
      pt := Y
      ι := {
        app := fun i ↦ nomatch i
        naturality := by
          intro i
          exact nomatch i } }
    uniq := by
      intro arrow
      apply hK.hom_ext
      intro i
      exact nomatch i }
  exact IsInitial.ofUnique K.pt

end SheafCohomologyExamples.LimitConstructionClient
