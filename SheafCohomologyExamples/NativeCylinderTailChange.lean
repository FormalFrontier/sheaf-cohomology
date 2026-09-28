/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: worker-b Hive Task hive-request-a52411214e83b3e8cc82da1235a39fa07761c413, UID 53f2275c-67d7-4642-adfe-75d218c8d1a9
Planning: worker-a Hive Task hive-request-4fa22ae4ca0e9c3b33a75a991b29940ba8a3b7eb, UID 3903dc2f-29a0-4761-a886-cee3408f2c3e
Dependencies: native cylinder and open naturality by their credited upstream authors
-/
module
import SheafCohomology.NativeCylinderTailChange

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeCylinderTailChange

attribute [local instance] hasColimit_cylinderSections_betweenTail

private theorem genericTailCoprojection
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    {C : Type (v + 1)} [Category.{v} C]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} C)
    (i0 j : ι) (h : i0 ≤ j) (U : Opens (S.obj (op i0)))
    [HasColimit (cylinderSections S i0 U)] (k : Set.Ici j) :
    colimit.ι (cylinderSections S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))) k ≫
      (cylinderSectionsTailColimitIso S i0 j h U).hom =
    (cylinderSectionsTailIso S i0 j h U).hom.app k ≫
      colimit.ι (cylinderSections S i0 U) ((betweenTailInclusion i0 j h).obj k) := by
  letI := hasColimit_cylinderSections_betweenTail S i0 j h U
  exact colimit_ι_cylinderSectionsTailColimitIso S i0 j h U k

private theorem genericConeStageSquare
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    {C : Type (v + 1)} [Category.{v} C]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} C)
    (i0 j : ι) (h : i0 ≤ j) (U : Opens (S.obj (op i0)))
    [HasColimit (cylinderSections S i0 U)] (m : Cone S) (k : Set.Ici j) :
    eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj (S.obj (op k.1))
        (stageOpen S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) k)).symm ≫
      colimit.ι (cylinderSections S j
        (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))) k ≫
      (cylinderSectionsTailColimitIso S i0 j h U).hom ≫
      cylinderSectionsComparison S i0 m U =
    eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj (S.obj (op k.1))
        (stageOpen S j (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) k)).symm ≫
      colimit.ι (cylinderSections S j
        (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))) k ≫
      cylinderSectionsComparison S j m (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) ≫
      eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
        (coneOpen_betweenTail S i0 j h U m)) := by
  letI := hasColimit_cylinderSections_betweenTail S i0 j h U
  simpa only [Category.assoc] using congrArg
    (fun arrow => eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
      (S.obj (op k.1)) (stageOpen S j
        (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0)) k)).symm ≫
        colimit.ι (cylinderSections S j
          (stageOpen S i0 U (⟨j, h⟩ : Set.Ici i0))) k ≫ arrow)
    (cylinderSectionsComparison_betweenTail S i0 j h U m)

private theorem ringTailSquare
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (R : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 j : ι) (h : i0 ≤ j) (U : Opens (R.obj (op i0))) (m : Cone R) :
    (cylinderSectionsTailColimitIso R i0 j h U).hom ≫
      nativeCommRingCylinderSectionsComparison R i0 m U =
    nativeCommRingCylinderSectionsComparison R j m
      (stageOpen R i0 U (⟨j, h⟩ : Set.Ici i0)) ≫
      eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
        (coneOpen_betweenTail R i0 j h U m)) := by
  rw [ringCylinderSectionsComparison_eq R i0 m U,
    ringCylinderSectionsComparison_eq R j m
      (stageOpen R i0 U (⟨j, h⟩ : Set.Ici i0))]
  exact cylinderSectionsComparison_betweenTail R i0 j h U m

private theorem additiveTailSquare
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (A : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i0 j : ι) (h : i0 ≤ j) (U : Opens (A.obj (op i0))) (m : Cone A) :
    (cylinderSectionsTailColimitIso A i0 j h U).hom ≫
      nativeAdditiveCylinderSectionsComparison A i0 m U =
    nativeAdditiveCylinderSectionsComparison A j m
      (stageOpen A i0 U (⟨j, h⟩ : Set.Ici i0)) ≫
      eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
        (coneOpen_betweenTail A i0 j h U m)) := by
  rw [additiveCylinderSectionsComparison_eq A i0 m U,
    additiveCylinderSectionsComparison_eq A j m
      (stageOpen A i0 U (⟨j, h⟩ : Set.Ici i0))]
  exact cylinderSectionsComparison_betweenTail A i0 j h U m

end SheafCohomologyExamples.NativeCylinderTailChange
