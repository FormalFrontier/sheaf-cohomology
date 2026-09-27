/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier worker-b Hive Task hive-request-bf36c0a2309835a3fdfa6d14f20ebde4191ab672
-/
module
import SheafCohomology.NativeStageSectionColimit

set_option warningAsError true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeStageSectionColimit

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace (Type v))
    (c : Cone (N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).map f))

include hc hstage htransition in
theorem colimMap_coneSections_cancel
    (x y : colimit (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ))
    (heq : colimMap (SheafCohomology.ConePullbackSections.coneSections N c) x =
      colimMap (SheafCohomology.ConePullbackSections.coneSections N c) y) :
    x = y :=
  ((CategoryTheory.isIso_iff_bijective _).mp
    (AlgebraicGeometry.SheafedSpace.isIso_colimMap_coneSections
      N c hc hstage htransition)).1 heq

include hc hstage htransition in
theorem conePullback_coprojection_inverse (i : J)
    (s : (AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).obj i) :
    ∃ x : colimit (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ),
      colimMap (SheafCohomology.ConePullbackSections.coneSections N c) x =
        colimit.ι (AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
          SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)) i s := by
  let S : J ⥤ Type v := N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ
  let P : J ⥤ Type v := AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
    SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)
  let η : S ⟶ P := SheafCohomology.ConePullbackSections.coneSections N c
  letI : IsIso (colimMap η) :=
    AlgebraicGeometry.SheafedSpace.isIso_colimMap_coneSections
      N c hc hstage htransition
  refine ⟨inv (colimMap η) (colimit.ι P i s), ?_⟩
  simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using
    (ConcreteCategory.congr_hom (IsIso.inv_hom_id (colimMap η)) (colimit.ι P i s))

end SheafCohomologyExamples.NativeStageSectionColimit
