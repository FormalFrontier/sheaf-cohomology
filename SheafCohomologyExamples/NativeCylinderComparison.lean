/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.NativeCylinderComparison

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeCylinderComparison

/-- For any open, including an empty one, an ordinary-import consumer obtains
the native projection, both base identities, and the original-stage section. -/
private theorem chosen_projection_and_original_stage
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)) (i0 : ι)
    (m : Cone N) (hm : IsLimit m) (U0 : Opens (N.obj (op i0)))
    (i : Set.Ici i0) :
    ((chosenLimitIso N i0 m hm U0).inv ≫
      (SheafedSpace.limitConeOfSpaceCone (Type v) (restricted N i0 U0)
        ((SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0))
        (restrictedSpaceIsLimit N i0 m hm U0)).cone.π.app (op i) =
      (restrictedCone N i0 m U0).π.app (op i)) ∧
    ((chosenLimitIso N i0 m hm U0).hom.hom.base = 𝟙 _) ∧
    ((chosenLimitIso N i0 m hm U0).inv.hom.base = 𝟙 _) ∧
    (eqToHom (SheafedSpace.restrict_Γ_obj
        (N.obj (op i.1)) (stageOpen N i0 U0 i)).symm ≫
        colimit.ι ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
          restrictedGlobalSectionsComparison N i0 m hm U0 =
      (m.π.app (op i.1)).hom.c.app (op (stageOpen N i0 U0 i)) ≫
        eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage N i0 m U0 i).symm)) := by
  exact ⟨chosenLimitIso_inv_projection N i0 m hm U0 (op i),
    chosenLimitIso_hom_base N i0 m hm U0,
    chosenLimitIso_inv_base N i0 m hm U0,
    originalStage_restrictedGlobalSectionsComparison N i0 m hm U0 i⟩

end SheafCohomologyExamples.NativeCylinderComparison
