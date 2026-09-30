/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
import SheafCohomology.NativeCommRingCylinderSections

set_option warningAsError true
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeCommRingCylinderSections

open AlgebraicGeometry
open SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 : ι) (m : Cone S) (U0 : Opens (S.obj (op i0)))

private theorem detect_original_projection_equality (hm : IsLimit m)
    (hstage : ∀ k : ιᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget CommRingCat.{v}).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget CommRingCat.{v}).map f))
    (hU0 : IsCompact (U0 : Set (S.obj (op i0))))
    (i : Set.Ici i0)
    (a b : (S.obj (op i.1)).presheaf.obj (op (stageOpen S i0 U0 i))) :
    (eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i) a =
    (eqToHom (SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i) b ↔
    ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
      eqToHom (congrArg
        (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
        (coneOpen_eq_stage S i0 m U0 i).symm)) a =
    ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
      eqToHom (congrArg
        (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
        (coneOpen_eq_stage S i0 m U0 i).symm)) b := by
  let stageLeg := eqToHom (SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ) i
  let originalLeg := (m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
      eqToHom (congrArg
        (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
        (coneOpen_eq_stage S i0 m U0 i).symm)
  let comparison := nativeCommRingCylinderSectionsComparison S i0 m U0
  letI : IsIso comparison :=
    isIso_nativeCommRingCylinderSectionsComparison S i0 m U0
      hm hstage htransition hU0
  have hinjective : Function.Injective comparison := by
    intro x y hxy
    have h := congrArg (fun z => (inv comparison) z) hxy
    simpa only [← CommRingCat.comp_apply, IsIso.hom_inv_id,
      CommRingCat.id_apply] using h
  have hcompare : stageLeg ≫ comparison = originalLeg :=
    originalStage_nativeCommRingCylinderSectionsComparison S i0 m U0 i
  have happly (t : (S.obj (op i.1)).presheaf.obj (op (stageOpen S i0 U0 i))) :
      comparison (stageLeg t) = originalLeg t := by
    simpa only [CommRingCat.comp_apply] using
      congrArg (fun arrow => arrow t) hcompare
  change stageLeg a = stageLeg b ↔ originalLeg a = originalLeg b
  constructor
  · intro h
    calc
      originalLeg a = comparison (stageLeg a) := (happly a).symm
      _ = comparison (stageLeg b) := congrArg comparison h
      _ = originalLeg b := happly b
  · intro h
    apply hinjective
    calc
      comparison (stageLeg a) = originalLeg a := happly a
      _ = originalLeg b := h
      _ = comparison (stageLeg b) := (happly b).symm

private theorem product_from_some_original_stage (hm : IsLimit m)
    (hstage : ∀ k : ιᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget CommRingCat.{v}).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget CommRingCat.{v}).map f))
    (hU0 : IsCompact (U0 : Set (S.obj (op i0))))
    (r s : m.pt.presheaf.obj (op (coneOpen S i0 m U0))) :
    ∃ (i : Set.Ici i0)
        (a : (S.obj (op i.1)).presheaf.obj (op (stageOpen S i0 U0 i))),
      ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
        eqToHom (congrArg
          (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage S i0 m U0 i).symm)) a = r * s :=
  exists_nativeCommRingCylinderSections_stage S i0 m U0 hm hstage htransition hU0 (r * s)

private theorem empty_open_isIso (hm : IsLimit m)
    (hstage : ∀ k : ιᵒᵖ,
      SpectralSpace ((S ⋙ SheafedSpace.forget CommRingCat.{v}).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ SheafedSpace.forget CommRingCat.{v}).map f)) :
    IsIso (nativeCommRingCylinderSectionsComparison S i0 m
      (⊥ : Opens (S.obj (op i0)))) := by
  apply isIso_nativeCommRingCylinderSectionsComparison S i0 m
    (⊥ : Opens (S.obj (op i0))) hm hstage htransition
  simp

omit [IsDirectedOrder ι] in
private theorem selected_tail_stage_arrow (i0 : ι) (m : Cone S)
    (U0 : Opens (S.obj (op i0))) :
    eqToHom (SheafedSpace.restrict_Γ_obj (S.obj (op i0))
        (stageOpen S i0 U0 ⟨i0, le_refl i0⟩)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ SheafedSpace.Γ)
        (⟨i0, le_refl i0⟩ : Set.Ici i0) ≫
        nativeCommRingCylinderSectionsComparison S i0 m U0 =
      (m.π.app (op i0)).hom.c.app
          (op (stageOpen S i0 U0 ⟨i0, le_refl i0⟩)) ≫
        eqToHom (congrArg
          (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage S i0 m U0 ⟨i0, le_refl i0⟩).symm) :=
  originalStage_nativeCommRingCylinderSectionsComparison S i0 m U0
    ⟨i0, le_refl i0⟩

end SheafCohomologyExamples.NativeCommRingCylinderSections
