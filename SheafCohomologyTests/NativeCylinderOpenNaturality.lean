/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Example for the native cylinder open-variable naturality API.
-/


module
import SheafCohomology.NativeCylinderOpenNaturality

set_option warningAsError true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace SheafCohomologyExamples.NativeCylinderOpenNaturality

open AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

private theorem ringOriginalNamedSectionRestriction
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 : ι) (m : Cone S) (U V : Opens (S.obj (op i0))) (h : U ≤ V)
    (i : Set.Ici i0) :
    ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 V i)) ≫
      eqToHom (congrArg
        (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
        (coneOpen_eq_stage S i0 m V i).symm)) ≫
      m.pt.presheaf.map (homOfLE (coneOpen_mono S i0 m h)).op =
    eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 V i)).symm ≫
      colimit.ι (cylinderSections S i0 V) i ≫
      colimMap (stageSectionsRestriction S i0 U V h) ≫
      nativeCommRingCylinderSectionsComparison S i0 m U := by
  rw [← originalStage_nativeCommRingCylinderSectionsComparison S i0 m V i]
  simpa only [cylinderSections, Category.assoc] using (congrArg
    (fun arrow => eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 V i)).symm ≫
        colimit.ι (cylinderSections S i0 V) i ≫ arrow)
    (ringCylinderSectionsComparison_restrict S i0 m U V h)).symm

private theorem ringStageRepresentativeRestriction
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 : ι) (m : Cone S) (U V : Opens (S.obj (op i0))) (h : U ≤ V)
    (i : Set.Ici i0)
    (stageSection : (S.obj (op i.1)).presheaf.obj (op (stageOpen S i0 V i))) :
    (((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 V i)) ≫
      eqToHom (congrArg
        (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
        (coneOpen_eq_stage S i0 m V i).symm)) ≫
      m.pt.presheaf.map (homOfLE (coneOpen_mono S i0 m h)).op) stageSection =
    (eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 V i)).symm ≫
      colimit.ι (cylinderSections S i0 V) i ≫
      colimMap (stageSectionsRestriction S i0 U V h) ≫
      nativeCommRingCylinderSectionsComparison S i0 m U) stageSection :=
  congrArg (fun arrow => arrow stageSection)
    (ringOriginalNamedSectionRestriction S i0 m U V h i)

private theorem additiveOriginalNamedSectionRestriction
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i0 : ι) (m : Cone S) (U V : Opens (S.obj (op i0))) (h : U ≤ V)
    (i : Set.Ici i0) :
    ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 V i)) ≫
      eqToHom (congrArg
        (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
        (coneOpen_eq_stage S i0 m V i).symm)) ≫
      m.pt.presheaf.map (homOfLE (coneOpen_mono S i0 m h)).op =
    eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 V i)).symm ≫
      colimit.ι (cylinderSections S i0 V) i ≫
      colimMap (stageSectionsRestriction S i0 U V h) ≫
      nativeAdditiveCylinderSectionsComparison S i0 m U := by
  rw [← originalStage_nativeAdditiveCylinderSectionsComparison S i0 m V i]
  simpa only [cylinderSections, Category.assoc] using (congrArg
    (fun arrow => eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
      (S.obj (op i.1)) (stageOpen S i0 V i)).symm ≫
        colimit.ι (cylinderSections S i0 V) i ≫ arrow)
    (additiveCylinderSectionsComparison_restrict S i0 m U V h)).symm

private theorem ringProperOpen
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 : ι) (m : Cone S) (U V : Opens (S.obj (op i0))) (h : U < V)
    (i : Set.Ici i0) :
    ((m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 V i)) ≫
      eqToHom (congrArg
        (fun O : Opens m.pt => m.pt.presheaf.obj (op O))
        (coneOpen_eq_stage S i0 m V i).symm)) ≫
      m.pt.presheaf.map (homOfLE (coneOpen_mono S i0 m h.le)).op =
    eqToHom (AlgebraicGeometry.SheafedSpace.restrict_Γ_obj
        (S.obj (op i.1)) (stageOpen S i0 V i)).symm ≫
      colimit.ι (cylinderSections S i0 V) i ≫
      colimMap (stageSectionsRestriction S i0 U V h.le) ≫
      nativeCommRingCylinderSectionsComparison S i0 m U :=
  ringOriginalNamedSectionRestriction S i0 m U V h.le i

private theorem additiveEmptyOpen
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i0 : ι) (m : Cone S) (V : Opens (S.obj (op i0))) :
    colimMap (stageSectionsRestriction S i0 (⊥ : Opens (S.obj (op i0))) V bot_le) ≫
      nativeAdditiveCylinderSectionsComparison S i0 m ⊥ =
    nativeAdditiveCylinderSectionsComparison S i0 m V ≫
      m.pt.presheaf.map (homOfLE (coneOpen_mono S i0 m bot_le)).op :=
  additiveCylinderSectionsComparison_restrict S i0 m ⊥ V bot_le

private theorem ringRestrictionComposition
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} CommRingCat.{v})
    (i0 : ι) (U V W : Opens (S.obj (op i0))) (hUV : U ≤ V) (hVW : V ≤ W) :
    stageSectionsRestriction S i0 V W hVW ≫
      stageSectionsRestriction S i0 U V hUV =
        stageSectionsRestriction S i0 U W (hUV.trans hVW) :=
  stageSectionsRestriction_comp S i0 U V W hUV hVW

private theorem additiveRestrictionIdentity
    {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (S : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} AddCommGrpCat.{v})
    (i0 : ι) (U : Opens (S.obj (op i0))) :
    stageSectionsRestriction S i0 U U (le_refl U) = 𝟙 (cylinderSections S i0 U) :=
  stageSectionsRestriction_id S i0 U

end SheafCohomologyExamples.NativeCylinderOpenNaturality
