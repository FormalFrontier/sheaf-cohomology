/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.NativeCylinderComparison
public import SpectralStoneDuality.Subspace

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global sections of compact-open native cylinders

For a directed opposite diagram of spectral sheafed spaces with spectral
transition maps, the actual native comparison from the restricted-stage
sections to sections over a compact open cylinder is invertible.
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

omit [IsDirectedOrder ι] in
private theorem spectralStage
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0)))) (i : (Set.Ici i0)ᵒᵖ) :
    SpectralSpace ((restricted N i0 U0 ⋙ SheafedSpace.forget (Type v)).obj i) := by
  letI : SpectralSpace (N.obj (op (unop i).1)) := hstage (op (unop i).1)
  have hc : IsCompact (stageOpen N i0 U0 (unop i) : Set (N.obj (op (unop i).1))) := by
    let base : Set.Ici i0 := ⟨i0, le_refl i0⟩
    let f : i ⟶ op base := (homOfLE (show base ≤ unop i from (unop i).2)).op
    have heq := stageOpen_map N i0 U0 f
    rw [stageOpen_base N i0 U0] at heq
    rw [heq]
    have hspectral : IsSpectralMap ((tailDiagram N i0).map f).hom.base :=
      htransition ((tailInclusion i0).op.map f)
    simpa only [Opens.map_coe] using hU0.preimage_of_isOpen hspectral U0.isOpen
  have hcarrier : ((restricted N i0 U0 ⋙ SheafedSpace.forget (Type v)).obj i) =
      (Opens.toTopCat (N.obj (op (unop i).1))).obj (stageOpen N i0 U0 (unop i)) := rfl
  rw [hcarrier]
  letI : CompactSpace ((Opens.toTopCat (N.obj (op (unop i).1))).obj
      (stageOpen N i0 U0 (unop i))) :=
    isCompact_univ_iff.mp
      ((stageOpen N i0 U0 (unop i)).isOpenEmbedding.isCompact_iff.mpr (by
        simpa only [Set.image_univ, Opens.set_range_inclusion'] using hc))
  exact (stageOpen N i0 U0 (unop i)).isOpenEmbedding.spectralSpace

omit [IsDirectedOrder ι] in
private theorem spectralStageMap
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0))))
    {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) :
    IsSpectralMap ((restricted N i0 U0 ⋙ SheafedSpace.forget (Type v)).map f) := by
  letI : SpectralSpace (N.obj (op (unop i).1)) := hstage (op (unop i).1)
  letI : SpectralSpace (N.obj (op (unop j).1)) := hstage (op (unop j).1)
  have hc : IsCompact (stageOpen N i0 U0 (unop i) : Set (N.obj (op (unop i).1))) := by
    let base : Set.Ici i0 := ⟨i0, le_refl i0⟩
    let f0 : i ⟶ op base := (homOfLE (show base ≤ unop i from (unop i).2)).op
    have heq := stageOpen_map N i0 U0 f0
    rw [stageOpen_base N i0 U0] at heq
    rw [heq]
    have hspectral : IsSpectralMap ((tailDiagram N i0).map f0).hom.base :=
      htransition ((tailInclusion i0).op.map f0)
    simpa only [Opens.map_coe] using hU0.preimage_of_isOpen hspectral U0.isOpen
  have hincl : IsSpectralMap
      ((N.obj (op (unop i).1)).ofRestrict
        (stageOpen N i0 U0 (unop i)).isOpenEmbedding).hom.base := by
    have hinclSubtype := IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
      (hc.isRetrocompact (stageOpen N i0 U0 (unop i)).isOpen)
    rw [SheafedSpace.ofRestrict_hom_base]
    convert hinclSubtype using 1 <;> rfl
  have hcomp : IsSpectralMap
      (((tailDiagram N i0).map f).hom.base ∘
        ((N.obj (op (unop i).1)).ofRestrict
          (stageOpen N i0 U0 (unop i)).isOpenEmbedding).hom.base) :=
    (htransition ((tailInclusion i0).op.map f)).comp hincl
  change IsSpectralMap (stageMap N i0 U0 f).hom.base
  apply SpectralStoneDuality.isSpectralMap_to_subtype_of_comp
  convert hcomp using 1
  all_goals try rfl
  have hbase := congrArg (fun arrow => arrow.hom.base) (stageMap_fac N i0 U0 f)
  have hfunc := congrArg
    (fun arrow : (stage N i0 U0 i : TopCat) ⟶ (N.obj (op (unop j).1) : TopCat) =>
      (arrow : _ → _)) hbase
  let target : TopCat := N.obj (op (unop j).1)
  let restrictedTarget : TopCat := stage N i0 U0 j
  have hj : (Subtype.val : restrictedTarget → target) =
      (stageOpen N i0 U0 (unop j)).inclusion' := by
    funext point
    rfl
  funext point
  exact (congrFun hj ((stageMap N i0 U0 f).hom.base point)).trans
    (congrFun hfunc point)

/-- The actual restricted-cylinder comparison is invertible for compact open
sections of a spectral directed inverse system. -/
theorem isIso_restrictedGlobalSectionsComparison
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0)))) :
    IsIso (restrictedGlobalSectionsComparison N i0 m hm U0) := by
  let R := restricted N i0 U0
  let cR := (SheafedSpace.forget (Type v)).mapCone (restrictedCone N i0 m U0)
  let hcR : IsLimit cR := restrictedSpaceIsLimit N i0 m hm U0
  have hRstage : ∀ k : (Set.Ici i0)ᵒᵖ,
      SpectralSpace ((R ⋙ SheafedSpace.forget (Type v)).obj k) :=
    spectralStage N i0 U0 hstage htransition hU0
  have hRtransition : ∀ {k l : (Set.Ici i0)ᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((R ⋙ SheafedSpace.forget (Type v)).map f) :=
    fun {_ _} f => spectralStageMap N i0 U0 hstage htransition hU0 f
  have hnative : IsIso (SheafedSpace.nativeGlobalSectionsComparison R cR hcR) :=
    SheafedSpace.isIso_nativeGlobalSectionsComparison R cR hcR hRstage hRtransition
  have hcomparison : restrictedGlobalSectionsComparison N i0 m hm U0 =
      SheafedSpace.nativeGlobalSectionsComparison R cR hcR ≫
        SheafedSpace.Γ.map (chosenLimitIso N i0 m hm U0).inv.op ≫
          eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen N i0 m U0)) := by
    apply colimit.hom_ext
    intro i
    rw [colimit_ι_restrictedGlobalSectionsComparison,
      ← Category.assoc, ← Category.assoc,
      SheafedSpace.colimit_ι_nativeGlobalSectionsComparison,
      ← SheafedSpace.Γ.map_comp, ← op_comp,
      chosenLimitIso_inv_projection]
  rw [hcomparison]
  exact IsIso.comp_isIso' hnative (IsIso.comp_isIso' inferInstance inferInstance)

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
