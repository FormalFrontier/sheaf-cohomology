/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.AbelianForget.ConePullbackCocone
import SheafCohomology.AbelianForget.FilteredColimits
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Import-only clients of the native additive-forgetful cocone comparison

The two arrows of `Fin 3` below are nonidentity index arrows. Their images in
an arbitrary diagram may nevertheless be identities. All cones are actual
cones of sheafed spaces, not assumed to be limiting.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.SheafedSpace.AbelianForget
open TopCat.Sheaf.AbelianForget

universe v

namespace SheafCohomologyExamples.AbelianForgetConePullbackCoconeClient

private def first : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def second : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

variable (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) (c : Cone S)

private theorem stage_first :
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone c)).ι.app (0 : Fin 3) =
    (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom.app
        (0 : Fin 3) ≫
      (underlyingSheaf (c.pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (0 : Fin 3)) :=
  conePullbackCocone_forget_ι S c (0 : Fin 3)

private theorem stage_middle :
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone c)).ι.app (1 : Fin 3) =
    (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom.app
        (1 : Fin 3) ≫
      (underlyingSheaf (c.pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (1 : Fin 3)) :=
  conePullbackCocone_forget_ι S c (1 : Fin 3)

private theorem stage_last :
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone c)).ι.app (2 : Fin 3) =
    (conePullbackIso S ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom.app
        (2 : Fin 3) ≫
      (underlyingSheaf (c.pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c).ι.app (2 : Fin 3)) :=
  conePullbackCocone_forget_ι S c (2 : Fin 3)

private theorem first_index_triangle :
    (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
      ((SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c))).map first ≫
      (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
        (underlying.mapCone c)).ι.app (1 : Fin 3) =
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone c)).ι.app (0 : Fin 3) :=
  (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
    (underlying.mapCone c)).w first

private theorem second_index_triangle :
    (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
      ((SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c))).map second ≫
      (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
        (underlying.mapCone c)).ι.app (2 : Fin 3) =
    (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
      (underlying.mapCone c)).ι.app (1 : Fin 3) :=
  (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
    (underlying.mapCone c)).w second

private theorem desc_fin3
    [hA : HasColimit (SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))]
    [hAU : HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{v} S
      ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)) ⋙
        underlyingSheaf (c.pt : TopCat))]
    [hT : HasColimit (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
      ((SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c)))] :
    (@colimMap _ _ _ _ _ _ hAU hT (conePullbackIso S
        ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c)).hom ≫
        colimit.post (SheafedSpace.conePullback AddCommGrpCat.{v} S
          ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))
          (underlyingSheaf (c.pt : TopCat))) ≫
      (underlyingSheaf (c.pt : TopCat)).map
        (colimit.desc (SheafedSpace.conePullback AddCommGrpCat.{v} S
          ((SheafedSpace.forget AddCommGrpCat.{v}).mapCone c))
          (SheafedSpace.conePullbackCocone AddCommGrpCat.{v} S c)) =
      colimit.desc (SheafedSpace.conePullback (Type v) (S ⋙ underlying)
        ((SheafedSpace.forget (Type v)).mapCone (underlying.mapCone c)))
        (SheafedSpace.conePullbackCocone (Type v) (S ⋙ underlying)
          (underlying.mapCone c)) :=
  conePullbackCocone_forget_desc S c

private theorem filtered_colimit_comparison_isIso
    (T : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0}) (native : Cone T)
    [hA : HasColimit (SheafedSpace.conePullback AddCommGrpCat.{0} T
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native))]
    [hAU : HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{0} T
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native)) ⋙
        underlyingSheaf (native.pt : TopCat))]
    [hT : HasColimit (SheafedSpace.conePullback (Type 0) (T ⋙ underlying)
      ((SheafedSpace.forget (Type 0)).mapCone (underlying.mapCone native)))] :
    IsIso (@colimMap _ _ _ _ _ _ hAU hT (conePullbackIso T
        ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native)).hom ≫
        colimit.post (SheafedSpace.conePullback AddCommGrpCat.{0} T
          ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native))
          (underlyingSheaf (native.pt : TopCat))) := by
  have hMap : IsIso (@colimMap _ _ _ _ _ _ hAU hT (conePullbackIso T
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native)).hom) := by
    have hθ : IsIso (conePullbackIso T
        ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native)).hom := inferInstance
    exact @isIso_colimMap _ _ _ _ _ _ hAU hT _ hθ
  have hAUcanonical : HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{0} T
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native)) ⋙
      underlyingSheaf ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native).pt) := by
    change HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{0} T
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native)) ⋙
        underlyingSheaf (native.pt : TopCat))
    exact hAU
  have hPost : IsIso (colimit.post
      (SheafedSpace.conePullback AddCommGrpCat.{0} T
        ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native))
      (underlyingSheaf (native.pt : TopCat))) :=
    @canonicalComparison_isIso
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native).pt (Fin 3) inferInstance
      (SheafedSpace.conePullback AddCommGrpCat.{0} T
        ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone native)) inferInstance hA hAUcanonical
  exact IsIso.comp_isIso' hMap hPost

/-- A native additive sheafed space whose carrier is genuinely empty. -/
private def emptySheafedSpace (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0}) :
    SheafedSpace AddCommGrpCat.{0} where
  carrier := TopCat.of PEmpty
  presheaf := F.1
  IsSheaf := F.2

private def emptyDiagram (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0}) :
    (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0} :=
  (Functor.const _).obj (emptySheafedSpace F)

private def emptyCarrierCone (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0}) :
    Cone (emptyDiagram F) where
  pt := emptySheafedSpace F
  π := {
    app := fun _ ↦ 𝟙 _
    naturality := by
      intro i j arrow
      simp [emptyDiagram] }

private theorem empty_vertex_carrier (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0}) :
    ((emptyCarrierCone F).pt : TopCat) = TopCat.of PEmpty := rfl

private theorem empty_stage (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0}) :
    (SheafedSpace.conePullbackCocone (Type 0) (emptyDiagram F ⋙ underlying)
      (underlying.mapCone (emptyCarrierCone F))).ι.app (0 : Fin 3) =
    (conePullbackIso (emptyDiagram F)
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone (emptyCarrierCone F))).hom.app
        (0 : Fin 3) ≫
      (underlyingSheaf ((emptyCarrierCone F).pt : TopCat)).map
        ((SheafedSpace.conePullbackCocone AddCommGrpCat.{0} (emptyDiagram F)
          (emptyCarrierCone F)).ι.app (0 : Fin 3)) :=
  conePullbackCocone_forget_ι (emptyDiagram F) (emptyCarrierCone F) (0 : Fin 3)

private theorem empty_desc (F : (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0})
    [hA : HasColimit (SheafedSpace.conePullback AddCommGrpCat.{0} (emptyDiagram F)
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone (emptyCarrierCone F)))]
    [hAU : HasColimit ((SheafedSpace.conePullback AddCommGrpCat.{0} (emptyDiagram F)
      ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone (emptyCarrierCone F))) ⋙
        underlyingSheaf ((emptyCarrierCone F).pt : TopCat))]
    [hT : HasColimit (SheafedSpace.conePullback (Type 0)
      (emptyDiagram F ⋙ underlying)
      ((SheafedSpace.forget (Type 0)).mapCone
        (underlying.mapCone (emptyCarrierCone F))))] :
    (@colimMap _ _ _ _ _ _ hAU hT (conePullbackIso (emptyDiagram F)
        ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone (emptyCarrierCone F))).hom ≫
        colimit.post (SheafedSpace.conePullback AddCommGrpCat.{0} (emptyDiagram F)
          ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone (emptyCarrierCone F)))
          (underlyingSheaf ((emptyCarrierCone F).pt : TopCat))) ≫
      (underlyingSheaf ((emptyCarrierCone F).pt : TopCat)).map
        (colimit.desc (SheafedSpace.conePullback AddCommGrpCat.{0} (emptyDiagram F)
          ((SheafedSpace.forget AddCommGrpCat.{0}).mapCone (emptyCarrierCone F)))
          (SheafedSpace.conePullbackCocone AddCommGrpCat.{0} (emptyDiagram F)
            (emptyCarrierCone F))) =
      colimit.desc (SheafedSpace.conePullback (Type 0) (emptyDiagram F ⋙ underlying)
        ((SheafedSpace.forget (Type 0)).mapCone
          (underlying.mapCone (emptyCarrierCone F))))
        (SheafedSpace.conePullbackCocone (Type 0) (emptyDiagram F ⋙ underlying)
          (underlying.mapCone (emptyCarrierCone F))) :=
  conePullbackCocone_forget_desc (emptyDiagram F) (emptyCarrierCone F)

end SheafCohomologyExamples.AbelianForgetConePullbackCoconeClient
