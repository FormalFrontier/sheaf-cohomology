/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.NativeCylinderLimit
public import SheafCohomology.NativeLimitGlobalSections
public import SheafCohomology.LimitPreservation
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Chosen native limits and the sections of a principal-tail cylinder

The native limit of a restricted diagram is compared to the literal restriction
of a chosen native limit. Its global-sections comparison is read at each original
stage, retaining the inverse-image and restriction-object transports.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)) (i0 : ι)
    (m : Cone N) (hm : IsLimit m) (U0 : Opens (N.obj (op i0)))

private instance tailNonempty : Nonempty (Set.Ici i0) := ⟨⟨i0, le_refl i0⟩⟩

private instance tailDirected : IsDirectedOrder (Set.Ici i0) :=
  ⟨fun i j => by
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i.1 j.1
    exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩⟩

private instance tailFiltered : IsFiltered (Set.Ici i0) := inferInstance

include hm

/-- Forgetting the constructed native restricted limit yields an actual
topological limit, by the published preservation theorem. -/
@[expose] def restrictedSpaceIsLimit :
    IsLimit ((SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0)) := by
  let R := restricted N i0 U0
  letI : PreservesLimit R (SheafedSpace.forget (Type v)) :=
    SheafedSpace.preservesLimitForgetOfHasLimit (Type v) R
  exact isLimitOfPreserves (SheafedSpace.forget (Type v))
    (restrictedIsLimit N i0 m hm U0)

/-- The chosen native limit of the restricted diagram is isomorphic to the
literal restriction of the original cone point. -/
def chosenLimitIso :
    (SheafedSpace.limitConeOfSpaceCone (Type v) (restricted N i0 U0)
      ((SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0))
      (restrictedSpaceIsLimit N i0 m hm U0)).cone.pt ≅
      (restrictedCone N i0 m U0).pt :=
  (SheafedSpace.limitConeOfSpaceCone (Type v) (restricted N i0 U0)
    ((SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0))
    (restrictedSpaceIsLimit N i0 m hm U0)).isLimit.conePointUniqueUpToIso
      (restrictedIsLimit N i0 m hm U0)

/-- The forward native isomorphism commutes with every restricted projection. -/
theorem chosenLimitIso_hom_projection (k : (Set.Ici i0)ᵒᵖ) :
    (chosenLimitIso N i0 m hm U0).hom ≫ (restrictedCone N i0 m U0).π.app k =
      (SheafedSpace.limitConeOfSpaceCone (Type v) (restricted N i0 U0)
        ((SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0))
        (restrictedSpaceIsLimit N i0 m hm U0)).cone.π.app k :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ k

/-- The inverse native isomorphism is the inverse of the restricted-cone
projection comparison, not merely an equality of underlying base maps. -/
theorem chosenLimitIso_inv_projection (k : (Set.Ici i0)ᵒᵖ) :
    (chosenLimitIso N i0 m hm U0).inv ≫
        (SheafedSpace.limitConeOfSpaceCone (Type v) (restricted N i0 U0)
          ((SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0))
          (restrictedSpaceIsLimit N i0 m hm U0)).cone.π.app k =
      (restrictedCone N i0 m U0).π.app k :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ k

/-- The forward native comparison has the identity as its underlying map on
the literal cylinder space. -/
theorem chosenLimitIso_hom_base :
    (chosenLimitIso N i0 m hm U0).hom.hom.base = 𝟙 _ := by
  let cR := (SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0)
  have hcR : IsLimit cR := restrictedSpaceIsLimit N i0 m hm U0
  let Q := SheafedSpace.limitConeOfSpaceCone (Type v) (restricted N i0 U0) cR hcR
  apply hcR.hom_ext
  intro k
  have h := chosenLimitIso_hom_projection N i0 m hm U0 k
  have hbase := congrArg (fun f : Q.cone.pt ⟶ (restricted N i0 U0).obj k => f.hom.base) h
  have hπ : cR.π.app k = ((restrictedCone N i0 m U0).π.app k).hom.base := rfl
  rw [hπ]
  simpa only [Functor.mapCone_π_app, SheafedSpace.forget, Functor.comp_obj,
    comp_hom_base, Category.id_comp,
    SheafedSpace.limitConeOfSpaceCone_π_base] using hbase

/-- The inverse native comparison also induces the identity on the literal
cylinder space. -/
theorem chosenLimitIso_inv_base :
    (chosenLimitIso N i0 m hm U0).inv.hom.base = 𝟙 _ := by
  let cR := (SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0)
  have hcR : IsLimit cR := restrictedSpaceIsLimit N i0 m hm U0
  let s := restrictedCone N i0 m U0
  apply hcR.hom_ext
  intro k
  have h := chosenLimitIso_inv_projection N i0 m hm U0 k
  have hbase := congrArg (fun f : s.pt ⟶ (restricted N i0 U0).obj k => f.hom.base) h
  have hπ : cR.π.app k = ((restrictedCone N i0 m U0).π.app k).hom.base := rfl
  rw [hπ]
  simpa only [Functor.mapCone_π_app, SheafedSpace.forget, Functor.comp_obj,
    comp_hom_base, Category.id_comp,
    SheafedSpace.limitConeOfSpaceCone_π_base] using hbase

/-- The actual colimit comparison, transported along the native isomorphism
and read as sections of the distinguished inverse-image open. -/
def restrictedGlobalSectionsComparison :
    colimit ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) ⟶
      m.pt.presheaf.obj (op (coneOpen N i0 m U0)) :=
  SheafedSpace.nativeGlobalSectionsComparison (restricted N i0 U0)
    ((SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0))
    (restrictedSpaceIsLimit N i0 m hm U0) ≫
    SheafedSpace.Γ.map (chosenLimitIso N i0 m hm U0).inv.op ≫
    eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen N i0 m U0))

/-- The actual comparison's leg is the global-sections map of the actual
native restricted projection, followed by the restriction-object cast. -/
theorem colimit_ι_restrictedGlobalSectionsComparison (i : Set.Ici i0) :
    colimit.ι ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
        restrictedGlobalSectionsComparison N i0 m hm U0 =
      SheafedSpace.Γ.map ((restrictedCone N i0 m U0).π.app (op i)).op ≫
        eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen N i0 m U0)) := by
  unfold restrictedGlobalSectionsComparison
  rw [← Category.assoc, ← Category.assoc,
    SheafedSpace.colimit_ι_nativeGlobalSectionsComparison]
  rw [← SheafedSpace.Γ.map_comp, ← op_comp,
    chosenLimitIso_inv_projection]

/-- On an original stage section, the constructed comparison is the actual
native cone projection's presheaf component, with the named inverse-image cast. -/
theorem originalStage_restrictedGlobalSectionsComparison (i : Set.Ici i0) :
    eqToHom (SheafedSpace.restrict_Γ_obj (N.obj (op i.1)) (stageOpen N i0 U0 i)).symm ≫
        colimit.ι ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
          restrictedGlobalSectionsComparison N i0 m hm U0 =
      (m.π.app (op i.1)).hom.c.app (op (stageOpen N i0 U0 i)) ≫
        eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
          (coneOpen_eq_stage N i0 m U0 i).symm) := by
  have hcomponent : coneComponent N i0 m U0 i =
      SheafedSpace.restrictOnNamedPreimage (m.π.app (op i.1))
        (stageOpen N i0 U0 i) (coneOpen N i0 m U0)
        (coneOpen_eq_stage N i0 m U0 i) := by
    haveI : Mono ((N.obj (op i.1)).ofRestrict
        (stageOpen N i0 U0 i).isOpenEmbedding) := inferInstance
    apply (cancel_mono ((N.obj (op i.1)).ofRestrict
      (stageOpen N i0 U0 i).isOpenEmbedding)).1
    exact (coneComponent_fac N i0 m U0 i).trans
      (SheafedSpace.restrictOnNamedPreimage_fac
        (m.π.app (op i.1)) (stageOpen N i0 U0 i)
        (coneOpen N i0 m U0) (coneOpen_eq_stage N i0 m U0 i)).symm
  calc
    _ = eqToHom (SheafedSpace.restrict_Γ_obj (N.obj (op i.1))
          (stageOpen N i0 U0 i)).symm ≫
          (colimit.ι ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ) i ≫
            restrictedGlobalSectionsComparison N i0 m hm U0) :=
        Category.assoc _ _ _
    _ = eqToHom (SheafedSpace.restrict_Γ_obj (N.obj (op i.1))
          (stageOpen N i0 U0 i)).symm ≫
          (SheafedSpace.Γ.map ((restrictedCone N i0 m U0).π.app (op i)).op ≫
            eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen N i0 m U0))) :=
        congrArg (eqToHom (SheafedSpace.restrict_Γ_obj (N.obj (op i.1))
          (stageOpen N i0 U0 i)).symm ≫ ·)
          (colimit_ι_restrictedGlobalSectionsComparison N i0 m hm U0 i)
    _ = _ := by
      simp only [restrictedCone]
      rw [hcomponent]
      exact
        (SheafedSpace.restrictOnNamedPreimage_Γ_map
          (m.π.app (op i.1)) (stageOpen N i0 U0 i)
          (coneOpen N i0 m U0) (coneOpen_eq_stage N i0 m U0 i))

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
