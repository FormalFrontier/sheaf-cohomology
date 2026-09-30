/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
public import SheafCohomology.NativeStageSectionLifting
public import Mathlib.CategoryTheory.Limits.Types.Filtered

public section

set_option warningAsError true

/-!
# Native stage sections and the cone-pullback colimit

For a filtered diagram of spectral sheafed spaces, the comparison from the
colimit of native global sections to the colimit of the actual cone-pullback
sections is an isomorphism of types.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))

include hc hstage htransition in
/-- The ordinary Type-colimit map of the literal cone-section transformation is
an isomorphism; no extra injectivity or surjectivity of stage transitions is needed. -/
theorem isIso_colimMap_coneSections :
    IsIso (colimMap (SheafCohomology.ConePullbackSections.coneSections N c)) := by
  classical
  let S : J ⥤ Type v := N.rightOp ⋙ SheafedSpace.Γ
  let P : J ⥤ Type v := SheafedSpace.conePullback (Type v) N c ⋙
    SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)
  let η : S ⟶ P := SheafCohomology.ConePullbackSections.coneSections N c
  change IsIso (colimMap η)
  apply (CategoryTheory.isIso_iff_bijective (colimMap η)).2
  have hleg (i : J) (a : S.obj i) :
      colimMap η (colimit.ι S i a) = colimit.ι P i (η.app i a) := by
    simpa only [ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom
        (SheafCohomology.ConePullbackSections.colimit_ι_colimMap_coneSections
          N c i) a)
  constructor
  · intro x y heq
    obtain ⟨i, a, b, ha, hb⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂
        (colimit.isColimit S) x y
    change colimit.ι S i a = x at ha
    change colimit.ι S i b = y at hb
    have heqStage : colimit.ι P i (η.app i a) =
        colimit.ι P i (η.app i b) := by
      rw [← hleg i a, ← hleg i b, ha, hb]
      exact heq
    obtain ⟨j, g, hg⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff'
        (colimit.isColimit P) (η.app i a) (η.app i b)).mp heqStage
    have hnat : η.app j (S.map g a) = η.app j (S.map g b) := by
      calc
        _ = P.map g (η.app i a) := by
          simpa only [ConcreteCategory.comp_apply] using
            (ConcreteCategory.congr_hom (η.naturality g) a)
        _ = P.map g (η.app i b) := hg
        _ = η.app j (S.map g b) := by
          simpa only [ConcreteCategory.comp_apply] using
            (ConcreteCategory.congr_hom (η.naturality g) b).symm
    obtain ⟨k, h, hh⟩ := exists_Γ_eq_of_pullback_unit_eq
      N c hc hstage htransition j (S.map g a) (S.map g b) (by
        change (SheafCohomology.ConePullbackSections.coneSections N c).app j
          (S.map g a) =
          (SheafCohomology.ConePullbackSections.coneSections N c).app j
            (S.map g b)
        simpa only [η, SheafCohomology.ConePullbackSections.coneSections_app] using hnat)
    exact ha.symm.trans ((Types.colimit_sound' (g ≫ h) (g ≫ h)
      (by simpa only [S, Functor.map_comp, ConcreteCategory.comp_apply] using hh)).trans hb)
  · intro y
    obtain ⟨i, s, hs⟩ := Types.jointly_surjective' (F := P) y
    obtain ⟨j, g, a, hlift⟩ := exists_native_stage_section_lift
      N c hc hstage htransition i s
    refine ⟨colimit.ι S j a, ?_⟩
    calc
      colimMap η (colimit.ι S j a) = colimit.ι P j (η.app j a) := hleg j a
      _ = colimit.ι P j (P.map g s) := by rw [hlift]
      _ = colimit.ι P i s := colimit.w_apply P g s
      _ = y := hs

end AlgebraicGeometry.SheafedSpace
