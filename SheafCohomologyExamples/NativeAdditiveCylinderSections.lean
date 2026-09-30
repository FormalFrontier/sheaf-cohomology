/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/

module
import SheafCohomology.NativeAdditiveCylinderSections

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeAdditiveCylinderSections

open AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i0 : ι) (m : Cone S) (U0 : Opens (S.obj (op i0)))
    (hm : IsLimit m)
    (hstage : ∀ k : ιᵒᵖ,
      SpectralSpace ((S ⋙ AlgebraicGeometry.SheafedSpace.forget AddCommGrpCat.{v}).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((S ⋙ AlgebraicGeometry.SheafedSpace.forget AddCommGrpCat.{v}).map f))
    (hU0 : IsCompact (U0 : Set (S.obj (op i0))))

include hm hstage htransition hU0 in
/-- Equality under the actual original projection detects equality of the
transported additive stage coprojections, even for empty opens. -/
private theorem originalStage_detects_transported_coprojection_additive
    (i : Set.Ici i0)
    (a b : (S.obj (op i.1)).presheaf.obj (op (stageOpen S i0 U0 i)))
    (h : ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
          eqToHom (congrArg
            (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
            (coneOpen_eq_stage S i0 m U0 i).symm)) a =
        ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
          eqToHom (congrArg
            (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
            (coneOpen_eq_stage S i0 m U0 i).symm)) b) :
    (eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i) a =
    (eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i) b := by
  let F := CategoryTheory.forget AddCommGrpCat.{v}
  let β := nativeAdditiveCylinderSectionsComparison S i0 m U0
  have hβ : IsIso β :=
    isIso_nativeAdditiveCylinderSectionsComparison S i0 m U0 hm hstage htransition hU0
  have hFβ : IsIso (F.map β) := Functor.map_isIso F β
  have hleg := originalStage_nativeAdditiveCylinderSectionsComparison S i0 m U0 i
  have hleg' := (Category.assoc
    (eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm)
    (colimit.ι ((restricted S i0 U0).rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i)
    (nativeAdditiveCylinderSectionsComparison S i0 m U0)).trans hleg
  have ha := ConcreteCategory.congr_hom hleg' a
  have hb := ConcreteCategory.congr_hom hleg' b
  apply ((isIso_iff_bijective (F.map β)).mp hFβ).1
  change β ((eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i) a) =
    β ((eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
      colimit.ι ((restricted S i0 U0).rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ) i) b)
  simpa only [ConcreteCategory.comp_apply] using ha.trans (h.trans hb.symm)

end SheafCohomologyExamples.NativeAdditiveCylinderSections
