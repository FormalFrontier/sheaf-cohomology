/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
import SheafCohomology.NativeAdditiveGlobalSections
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeAdditiveGlobalSections

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (S : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (m : Cone S) (hm : IsLimit m)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((S ⋙ AlgebraicGeometry.SheafedSpace.forget AddCommGrpCat.{v}).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ AlgebraicGeometry.SheafedSpace.forget AddCommGrpCat.{v}).map f))

include hm hstage htransition in
/-- Sections at the same additive stage agree under the original projection
if and only if they agree after an actual filtered transition. -/
theorem nativeProjection_eq_iff_eventually_eq (i : J)
    (a b : (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj i) :
    AlgebraicGeometry.SheafedSpace.Γ.map (m.π.app (op i)).op a =
        AlgebraicGeometry.SheafedSpace.Γ.map (m.π.app (op i)).op b ↔
      ∃ (j : J) (f : i ⟶ j),
        (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).map f a =
          (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).map f b := by
  let F := CategoryTheory.forget AddCommGrpCat.{v}
  let β := AlgebraicGeometry.SheafedSpace.nativeAdditiveGlobalSectionsComparison S m
  have hβ : IsIso β :=
    AlgebraicGeometry.SheafedSpace.isIso_nativeAdditiveGlobalSectionsComparison
      S m hm hstage htransition
  have hFβ : IsIso (F.map β) := Functor.map_isIso F β
  have hleg := AlgebraicGeometry.SheafedSpace.colimit_ι_nativeAdditiveGlobalSectionsComparison
    S m i
  have ha := ConcreteCategory.congr_hom hleg a
  have hb := ConcreteCategory.congr_hom hleg b
  have hType : IsColimit (F.mapCocone
      (colimit.cocone (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ))) :=
    isColimitOfPreserves F
      (colimit.isColimit (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ))
  have hstageEq :
      (colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i a =
        colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i b) ↔
        ∃ (j : J) (f : i ⟶ j),
          (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).map f a =
            (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).map f b := by
    exact Types.FilteredColimit.isColimit_eq_iff' hType a b
  constructor
  · intro h
    have hcol : colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i a =
        colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i b := by
      apply ((isIso_iff_bijective (F.map β)).mp hFβ).1
      change β (colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i a) =
        β (colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i b)
      simpa only [ConcreteCategory.comp_apply] using ha.trans (h.trans hb.symm)
    exact hstageEq.mp hcol
  · rintro ⟨j, f, h⟩
    have hcol : colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i a =
        colimit.ι (S.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i b :=
      hstageEq.mpr ⟨j, f, h⟩
    exact ha.symm.trans ((congrArg (fun x => (F.map β) x) hcol).trans hb)

end SheafCohomologyExamples.NativeAdditiveGlobalSections
