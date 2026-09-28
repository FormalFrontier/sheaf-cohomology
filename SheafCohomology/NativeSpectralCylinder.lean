/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Formal Frontier worker-b Hive Task hive-request-581a9584fa061c70e8f8581b23cc51bae1d3f5bf, UID 0eb3d3fc-0bb3-4098-ab2f-892fe8a763f4
Topology proof expression: Formal Frontier worker-b Hive Task hive-request-e8a25d6c5328e70c571fe96c3ac0b8102530eaa1, UID ddcebc71-0a10-45a6-b8cf-9606083d850e
-/
module
public import SheafCohomology.NativeCylinderLimit
public import SpectralStoneDuality.Subspace
public import Mathlib.Topology.Constructible

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Spectral compact-open cylinders

Native restrictions to inverse images of a compact open in a spectral inverse
system retain spectral stage spaces and spectral transition maps, independently
of the coefficient category or any chosen limit.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace.NativeCylinderLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι]
    {C : Type (v + 1)} [Category.{v} C]
    (N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C) (i0 : ι)
    (U0 : Opens (N.obj (op i0)))

omit [IsDirectedOrder ι] in
/-- The actual open native restrictions of spectral stages are spectral. -/
theorem spectralStage
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget C).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget C).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0)))) (i : (Set.Ici i0)ᵒᵖ) :
    SpectralSpace ((restricted N i0 U0 ⋙ SheafedSpace.forget C).obj i) := by
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
  have hcarrier : ((restricted N i0 U0 ⋙ SheafedSpace.forget C).obj i) =
      (Opens.toTopCat (N.obj (op (unop i).1))).obj (stageOpen N i0 U0 (unop i)) := rfl
  rw [hcarrier]
  letI : CompactSpace ((Opens.toTopCat (N.obj (op (unop i).1))).obj
      (stageOpen N i0 U0 (unop i))) :=
    isCompact_univ_iff.mp
      ((stageOpen N i0 U0 (unop i)).isOpenEmbedding.isCompact_iff.mpr (by
        simpa only [Set.image_univ, Opens.set_range_inclusion'] using hc))
  exact (stageOpen N i0 U0 (unop i)).isOpenEmbedding.spectralSpace

omit [IsDirectedOrder ι] in
/-- The actual native transition between compact-open restrictions is spectral. -/
theorem spectralStageMap
    (hstage : ∀ k : ιᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget C).obj k))
    (htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget C).map f))
    (hU0 : IsCompact (U0 : Set (N.obj (op i0))))
    {i j : (Set.Ici i0)ᵒᵖ} (f : i ⟶ j) :
    IsSpectralMap ((restricted N i0 U0 ⋙ SheafedSpace.forget C).map f) := by
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

end AlgebraicGeometry.SheafedSpace.NativeCylinderLimit
