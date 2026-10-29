/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
import SheafCohomology.NativeStageSectionColimit

/-!
# Ordinary-import checks for section colimits

These compiler regression checks exercise the section-colimit comparison
theorem through an ordinary import. They keep the explicit limit-cone,
spectral-stage and spectral-transition hypotheses visible.

The first check uses the Type-valued bijectivity interface to cancel the
comparison map. The second obtains a source-colimit preimage of each target
coprojection using a local `IsIso` instance and the inverse identity.

The target is the colimit of cone-pullback section sets over the top open of
the limit space. The witness is in the source colimit; no same-stage preimage
or global-section construction on a sheafed-space cone is asserted.
-/

set_option warningAsError true

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
  let : IsIso (colimMap η) :=
    AlgebraicGeometry.SheafedSpace.isIso_colimMap_coneSections
      N c hc hstage htransition
  refine ⟨inv (colimMap η) (colimit.ι P i s), ?_⟩
  simpa only [ConcreteCategory.comp_apply, CategoryTheory.id_apply] using
    (ConcreteCategory.congr_hom (IsIso.inv_hom_id (colimMap η)) (colimit.ι P i s))

end SheafCohomologyExamples.NativeStageSectionColimit
