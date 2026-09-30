/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
public import SheafCohomology.NativeStageSectionEquality

public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeStageSectionEquality

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace (Type v))
    (c : Cone (N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (hstage : ∀ k : Jᵒᵖ,
      SpectralSpace ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ AlgebraicGeometry.SheafedSpace.forget (Type v)).map f))

include hc hstage htransition in
/-- Perpetually distinct compact-open sections have distinct literal
projection-unit images. -/
theorem compact_unit_distinguishes (i : J)
    (V : Opens (N.obj (op i))) (hV : IsCompact (V : Set (N.obj (op i))))
    (a b : (N.obj (op i)).presheaf.obj (op V))
    (hne : ∀ (j : J) (g : i ⟶ j),
      (N.map g.op).hom.c.app (op V) a ≠
        (N.map g.op).hom.c.app (op V) b) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op V) a ≠
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op V) b := by
  intro heq
  obtain ⟨j, g, hab⟩ := AlgebraicGeometry.SheafedSpace.exists_stage_eq_of_pullback_unit_eq
    N c hc hstage htransition i V hV a b heq
  exact hne j g hab

include hc hstage htransition in
/-- The existing functor of stagewise global sections detects unequal unit
images when every one of its transition maps keeps the sections distinct. -/
theorem global_unit_distinguishes (i : J)
    (a b : (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj i)
    (hne : ∀ (j : J) (g : i ⟶ j),
      (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).map g a ≠
        (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).map g b) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
          (op (⊤ : Opens (N.obj (op i)))) a ≠
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
          (op (⊤ : Opens (N.obj (op i)))) b := by
  intro heq
  obtain ⟨j, g, hab⟩ := AlgebraicGeometry.SheafedSpace.exists_Γ_eq_of_pullback_unit_eq
    N c hc hstage htransition i a b heq
  exact hne j g hab

end SheafCohomologyExamples.NativeStageSectionEquality
