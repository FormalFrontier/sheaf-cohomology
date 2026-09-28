/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology.NativeSpectralCylinderSections

set_option warningAsError true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeSpectralCylinderSections

/-- An ordinary importer detects equality of two transported stage coprojection
images by their actual original-stage projection sections. The equality carries
both the restriction-object and inverse-image-open casts. -/
private theorem originalStage_detects_transported_coprojection
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)) (i0 : ι)
    (m : Cone N) (hm : IsLimit m) (U0 : Opens (N.obj (op i0)))
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0))))
    (i : Set.Ici i0)
    (section₁ section₂ : (N.obj (op i.1)).presheaf.obj (op (stageOpen N i0 U0 i)))
    (heq : ((m.π.app (op i.1)).hom.c.app (op (stageOpen N i0 U0 i)) ≫
        eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage N i0 m U0 i).symm)) section₁ =
      ((m.π.app (op i.1)).hom.c.app (op (stageOpen N i0 U0 i)) ≫
        eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage N i0 m U0 i).symm)) section₂) :
    (eqToHom (SheafedSpace.restrict_Γ_obj
        (N.obj (op i.1)) (stageOpen N i0 U0 i)).symm ≫
      colimit.ι ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) i) section₁ =
    (eqToHom (SheafedSpace.restrict_Γ_obj
        (N.obj (op i.1)) (stageOpen N i0 U0 i)).symm ≫
      colimit.ι ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) i) section₂ := by
  letI : IsIso (restrictedGlobalSectionsComparison N i0 m hm U0) :=
    isIso_restrictedGlobalSectionsComparison N i0 m hm U0 hstage htransition hU0
  have hinjective : Function.Injective (restrictedGlobalSectionsComparison N i0 m hm U0) :=
    ((CategoryTheory.isIso_iff_bijective _).mp inferInstance).1
  apply hinjective
  have hleg := originalStage_restrictedGlobalSectionsComparison N i0 m hm U0 i
  have hleg' := (Category.assoc
    (eqToHom (SheafedSpace.restrict_Γ_obj
      (N.obj (op i.1)) (stageOpen N i0 U0 i)).symm)
    (colimit.ι ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) i)
    (restrictedGlobalSectionsComparison N i0 m hm U0)).trans hleg
  have hsection₁ := congrArg (fun arrow :
    (N.obj (op i.1)).presheaf.obj (op (stageOpen N i0 U0 i)) ⟶
      m.pt.presheaf.obj (op (coneOpen N i0 m U0)) => arrow section₁) hleg'
  have hsection₂ := congrArg (fun arrow :
    (N.obj (op i.1)).presheaf.obj (op (stageOpen N i0 U0 i)) ⟶
      m.pt.presheaf.obj (op (coneOpen N i0 m U0)) => arrow section₂) hleg'
  simpa only [CategoryTheory.types_comp_apply] using
    hsection₁.trans (heq.trans hsection₂.symm)

end SheafCohomologyExamples.NativeSpectralCylinderSections
