/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Formal Frontier worker-b Hive Task hive-request-e5e544a630e9b84215130384682791cdebd0aea0
-/
module
import SheafCohomology.NativeStageSectionLifting

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeStageSectionLifting

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace (Type v))
    (c : Cone (N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).map f))

include hc hstage htransition in
theorem exists_later_global_sections (i : J)
    (s : (AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).obj i) :
    ∃ j : J, Nonempty ((N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj j) := by
  obtain ⟨j, _, nativeSection, _⟩ := AlgebraicGeometry.SheafedSpace.exists_native_stage_section_lift
    N c hc hstage htransition i s
  exact ⟨j, ⟨nativeSection⟩⟩

include hc hstage htransition in
theorem later_native_transition_preserves_lift (i : J)
    (s : (AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).obj i) :
    ∃ (j : J) (g : i ⟶ j)
      (nativeSection : (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj j),
      ∀ (k : J) (f : j ⟶ k),
        (SheafCohomology.ConePullbackSections.coneSections N c).app k
            ((N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).map f nativeSection) =
          (AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
            SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map
              (g ≫ f) s := by
  obtain ⟨j, g, nativeSection, hsection⟩ :=
    AlgebraicGeometry.SheafedSpace.exists_native_stage_section_lift
      N c hc hstage htransition i s
  refine ⟨j, g, nativeSection, ?_⟩
  intro k f
  have hnat := ConcreteCategory.congr_hom
    ((SheafCohomology.ConePullbackSections.coneSections N c).naturality f) nativeSection
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hsection] at hnat
  simpa only [ConcreteCategory.comp_apply, Functor.map_comp] using hnat

end SheafCohomologyExamples.NativeStageSectionLifting
