/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.PullbackCoherence
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Topology.Category.TopCat.Opens

public section

set_option warningAsError true

/-!
# Base change along an open subspace

For a continuous map `f : X ⟶ Y` and an open `V ⊆ Y`, this file constructs
the canonical pullback square on open subspaces, the associated direct- and
inverse-image comparisons for sheaves of types, and identifies them as mates.

The topological spaces, coefficients, and sheaf morphisms use the same universe,
as required by the current `TopCat.Sheaf.pullback` API.
-/

open CategoryTheory TopologicalSpace
open CategoryTheory.Functor CategoryTheory.Adjunction CategoryTheory.NatTrans
  CategoryTheory.TwoSquare

noncomputable section

universe v

namespace TopCat.Sheaf.OpenBaseChange

private def openAdjunction {X Y : TopCat.{v}} {i : X ⟶ Y}
    (hi : Topology.IsOpenEmbedding i) :
    hi.sheafPullback (Type v) ⊣ TopCat.Sheaf.pushforward (Type v) i :=
  let _ := hi.functor_isContinuous
  hi.isOpenMap.adjunction.sheafPushforwardContinuous
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)

private theorem openAdjunction_unit_app_hom_app
    {X Y : TopCat.{v}} {i : X ⟶ Y}
    (hi : Topology.IsOpenEmbedding i)
    (P : Y.Sheaf (Type v)) (W : (Opens Y)ᵒᵖ) :
    ((openAdjunction hi).unit.app P).hom.app W =
      P.1.map (hi.isOpenMap.adjunction.counit.app W.unop).op := by
  let _ := hi.functor_isContinuous
  exact CategoryTheory.Adjunction.sheafPushforwardContinuous_unit_app_hom_app
    hi.isOpenMap.adjunction (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) P W

private theorem openAdjunction_counit_app_hom_app
    {X Y : TopCat.{v}} {i : X ⟶ Y}
    (hi : Topology.IsOpenEmbedding i)
    (P : X.Sheaf (Type v)) (W : (Opens X)ᵒᵖ) :
    ((openAdjunction hi).counit.app P).hom.app W =
      P.1.map (hi.isOpenMap.adjunction.unit.app W.unop).op := by
  let _ := hi.functor_isContinuous
  exact CategoryTheory.Adjunction.sheafPushforwardContinuous_counit_app_hom_app
    hi.isOpenMap.adjunction (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) P W

private def comparison {X Y : TopCat.{v}} {i : X ⟶ Y}
    (hi : Topology.IsOpenEmbedding i) :
    TopCat.Sheaf.pullback (Type v) i ≅ hi.sheafPullback (Type v) :=
  CategoryTheory.Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) i)
    (openAdjunction hi)

private theorem pushforward_obj_obj_map {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : X.Sheaf (Type v)) {W W' : (Opens Y)ᵒᵖ} (g : W ⟶ W') :
    ((TopCat.Sheaf.pushforward (Type v) f).obj F).obj.map g =
      F.obj.map ((Opens.map f).map g.unop).op := by
  rfl

private theorem pushforward_comp_obj_obj_map {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Sheaf (Type v))
    {W W' : (Opens Z)ᵒᵖ} (h : W ⟶ W') :
    ((TopCat.Sheaf.pushforward (Type v) f ⋙
        TopCat.Sheaf.pushforward (Type v) g).obj F).obj.map h =
      F.obj.map ((Opens.map f).map ((Opens.map g).map h.unop)).op := by
  rfl

private theorem pushforward_map_hom_app {X Y : TopCat.{v}} (f : X ⟶ Y)
    {F G : X.Sheaf (Type v)} (g : F ⟶ G) (W : (Opens Y)ᵒᵖ) :
    ((TopCat.Sheaf.pushforward (Type v) f).map g).hom.app W =
      g.hom.app (Opposite.op ((Opens.map f).obj W.unop)) := by
  rfl

private theorem sheafPushforwardContinuousIso_hom_app_hom_app
    {C D A : Type*} [Category C] [Category D] [Category A]
    {F F' : C ⥤ D} (e : F ≅ F')
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K] [F'.IsContinuous J K]
    (X : CategoryTheory.Sheaf K A) (W : Cᵒᵖ) :
    ((Functor.sheafPushforwardContinuousIso e A J K).hom.app X).hom.app W =
      X.obj.map (e.inv.app W.unop).op := by
  rfl

private theorem conjugateEquiv_pullback_eqToHom {X Y : TopCat.{v}}
    {f g : X ⟶ Y} (h : f = g) :
    CategoryTheory.conjugateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g)
      (eqToHom (congrArg (TopCat.Sheaf.pullback (Type v)) h).symm) =
        eqToHom (congrArg (TopCat.Sheaf.pushforward (Type v)) h) := by
  subst h
  simp

/-- The canonical map from the inverse-image open subspace `f⁻¹(V)` to `V`. -/
@[expose] def preimageMap {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    (Opens.toTopCat X).obj ((Opens.map f).obj V) ⟶ (Opens.toTopCat Y).obj V :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨f x.1, x.2⟩
      continuous_toFun :=
        (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

/-- The inverse-image open square commutes literally in `TopCat`. -/
theorem preimageMap_comp_inclusion {X Y : TopCat.{v}} (f : X ⟶ Y)
    (V : Opens Y) :
    preimageMap f V ≫ V.inclusion' =
      ((Opens.map f).obj V).inclusion' ≫ f := by
  ext x
  rfl

/-- The canonical comparison of functors on opens for the inverse-image square. -/
@[expose] def preimageOpensIso {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    V.isOpenEmbedding.functor ⋙ Opens.map f ≅
      Opens.map (preimageMap f V) ⋙ ((Opens.map f).obj V).isOpenEmbedding.functor :=
  NatIso.ofComponents (fun W ↦ eqToIso (by
    apply Opens.ext
    ext x
    constructor
    · rintro ⟨y, hyW, hyx⟩
      have hxU : x ∈ ((Opens.map f).obj V : Opens X) := by
        change f x ∈ V
        rw [← hyx]
        exact y.2
      refine ⟨⟨x, hxU⟩, ?_, rfl⟩
      change (⟨f x, hxU⟩ : V) ∈ W
      have hyEq : y = (⟨f x, hxU⟩ : V) := by
        apply Subtype.ext
        exact hyx
      rwa [← hyEq]
    · rintro ⟨z, hzW, rfl⟩
      exact ⟨preimageMap f V z, hzW, rfl⟩))
    (fun _ ↦ Subsingleton.elim _ _)

private def naiveBaseChangeIso {X Y : TopCat.{v}} (f : X ⟶ Y)
    (V : Opens Y) :
    TopCat.Sheaf.pushforward (Type v) f ⋙
        V.isOpenEmbedding.sheafPullback (Type v) ≅
      ((Opens.map f).obj V).isOpenEmbedding.sheafPullback (Type v) ⋙
        TopCat.Sheaf.pushforward (Type v) (preimageMap f V) := by
  let _ := V.isOpenEmbedding.functor_isContinuous
  let _ := ((Opens.map f).obj V).isOpenEmbedding.functor_isContinuous
  exact
    Functor.sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫
      Functor.sheafPushforwardContinuousIso (preimageOpensIso f V) _ _ _ ≪≫
      (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm

/-- Direct-image base change along an open inverse-image square. -/
@[expose] def baseChangeIso {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    TopCat.Sheaf.pushforward (Type v) f ⋙
        TopCat.Sheaf.pullback (Type v) V.inclusion' ≅
      TopCat.Sheaf.pullback (Type v) ((Opens.map f).obj V).inclusion' ⋙
        TopCat.Sheaf.pushforward (Type v) (preimageMap f V) := by
  let hiV : Topology.IsOpenEmbedding V.inclusion' := V.isOpenEmbedding
  let _ := hiV.functor_isContinuous
  let U := (Opens.map f).obj V
  let hiU : Topology.IsOpenEmbedding U.inclusion' := U.isOpenEmbedding
  let _ := hiU.functor_isContinuous
  let openAdjV :
      hiV.sheafPullback (Type v) ⊣
        TopCat.Sheaf.pushforward (Type v) V.inclusion' :=
    hiV.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat Y).obj V))
      (Opens.grothendieckTopology Y)
  let openAdjU :
      hiU.sheafPullback (Type v) ⊣
        TopCat.Sheaf.pushforward (Type v) U.inclusion' :=
    hiU.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (Opens.grothendieckTopology X)
  let comparisonV := CategoryTheory.Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion') openAdjV
  let comparisonU := CategoryTheory.Adjunction.leftAdjointUniq
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) U.inclusion') openAdjU
  let naive :
      TopCat.Sheaf.pushforward (Type v) f ⋙
          V.isOpenEmbedding.sheafPullback (Type v) ≅
        U.isOpenEmbedding.sheafPullback (Type v) ⋙
          TopCat.Sheaf.pushforward (Type v) (preimageMap f V) := by
    exact
      Functor.sheafPushforwardContinuousComp _ _ _ _ _ _ ≪≫
        Functor.sheafPushforwardContinuousIso (preimageOpensIso f V) _ _ _ ≪≫
        (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm
  exact
    Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type v) f)
        comparisonV ≪≫
      naive ≪≫
      (Functor.isoWhiskerRight comparisonU
        (TopCat.Sheaf.pushforward (Type v) (preimageMap f V))).symm

private theorem baseChangeIso_eq_privateConstruction
    {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    baseChangeIso f V =
      let U := (Opens.map f).obj V
      Functor.isoWhiskerLeft (TopCat.Sheaf.pushforward (Type v) f)
          (comparison V.isOpenEmbedding) ≪≫
        naiveBaseChangeIso f V ≪≫
        (Functor.isoWhiskerRight (comparison U.isOpenEmbedding)
          (TopCat.Sheaf.pushforward (Type v) (preimageMap f V))).symm :=
  rfl

/-- The inverse-image comparison induced by composition and the commuting square. -/
@[expose] def pullbackSquareIso {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    TopCat.Sheaf.pullback (Type v) V.inclusion' ⋙
        TopCat.Sheaf.pullback (Type v) (preimageMap f V) ≅
      TopCat.Sheaf.pullback (Type v) f ⋙
        TopCat.Sheaf.pullback (Type v) ((Opens.map f).obj V).inclusion' := by
  let e : TopCat.Sheaf.pullback (Type v)
        (((Opens.map f).obj V).inclusion' ≫ f) ≅
      TopCat.Sheaf.pullback (Type v) (preimageMap f V ≫ V.inclusion') :=
    eqToIso (congrArg (TopCat.Sheaf.pullback (Type v))
      (preimageMap_comp_inclusion f V).symm)
  exact ((TopCat.Sheaf.pullbackCompIso (Type v)
      ((Opens.map f).obj V).inclusion' f) ≪≫
    e ≪≫
    (TopCat.Sheaf.pullbackCompIso (Type v) (preimageMap f V)
      V.inclusion').symm).symm

/-- The inverse-image comparison packaged as a `TwoSquare`. -/
@[expose] def pullbackSquare {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    TwoSquare
      (TopCat.Sheaf.pullback (Type v) V.inclusion')
      (TopCat.Sheaf.pullback (Type v) f)
      (TopCat.Sheaf.pullback (Type v) (preimageMap f V))
      (TopCat.Sheaf.pullback (Type v) ((Opens.map f).obj V).inclusion') :=
  (pullbackSquareIso f V).hom

/-- Direct-image open base change packaged as a `TwoSquare`. -/
@[expose] def baseChangeSquare {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y) :
    TwoSquare
      (TopCat.Sheaf.pushforward (Type v) f)
      (TopCat.Sheaf.pullback (Type v) ((Opens.map f).obj V).inclusion')
      (TopCat.Sheaf.pullback (Type v) V.inclusion')
      (TopCat.Sheaf.pushforward (Type v) (preimageMap f V)) :=
  (baseChangeIso f V).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private def pushforwardCompIso {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pushforward (Type v) f ⋙
        TopCat.Sheaf.pushforward (Type v) g ≅
      TopCat.Sheaf.pushforward (Type v) (f ≫ g) :=
  Iso.refl _

private def pushforwardSquareIso {X Y : TopCat.{v}} (f : X ⟶ Y)
    (V : Opens Y) :
    TopCat.Sheaf.pushforward (Type v) ((Opens.map f).obj V).inclusion' ⋙
        TopCat.Sheaf.pushforward (Type v) f ≅
      TopCat.Sheaf.pushforward (Type v) (preimageMap f V) ⋙
        TopCat.Sheaf.pushforward (Type v) V.inclusion' :=
  pushforwardCompIso ((Opens.map f).obj V).inclusion' f ≪≫
    eqToIso (congrArg (TopCat.Sheaf.pushforward (Type v))
      (preimageMap_comp_inclusion f V).symm) ≪≫
    (pushforwardCompIso (preimageMap f V) V.inclusion').symm

private def pushforwardSquare {X Y : TopCat.{v}} (f : X ⟶ Y)
    (V : Opens Y) :
    TwoSquare
      (TopCat.Sheaf.pushforward (Type v) ((Opens.map f).obj V).inclusion')
      (TopCat.Sheaf.pushforward (Type v) (preimageMap f V))
      (TopCat.Sheaf.pushforward (Type v) f)
      (TopCat.Sheaf.pushforward (Type v) V.inclusion') :=
  (pushforwardSquareIso f V).hom

private def naiveBaseChangeSquare {X Y : TopCat.{v}} (f : X ⟶ Y)
    (V : Opens Y) :
    TwoSquare
      (TopCat.Sheaf.pushforward (Type v) f)
      (((Opens.map f).obj V).isOpenEmbedding.sheafPullback (Type v))
      (V.isOpenEmbedding.sheafPullback (Type v))
      (TopCat.Sheaf.pushforward (Type v) (preimageMap f V)) :=
  (naiveBaseChangeIso f V).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem naiveBaseChangeSquare_mate {X Y : TopCat.{v}}
    (f : X ⟶ Y) (V : Opens Y) :
    CategoryTheory.mateEquiv
      (openAdjunction ((Opens.map f).obj V).isOpenEmbedding)
      (openAdjunction V.isOpenEmbedding)
      (naiveBaseChangeSquare f V) = pushforwardSquare f V := by
  let _ := V.isOpenEmbedding.functor_isContinuous
  let _ := ((Opens.map f).obj V).isOpenEmbedding.functor_isContinuous
  rw [mateEquiv_apply]
  apply TwoSquare.ext
  intro F
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  simp only [naiveBaseChangeSquare, naiveBaseChangeIso, pushforwardSquare,
    pushforwardSquareIso, pushforwardCompIso,
    NatTrans.comp_app,
    rightUnitor_inv_app, Functor.whiskerLeft_app, associator_hom_app,
    associator_inv_app, Functor.whiskerRight_app, leftUnitor_hom_app,
    Functor.comp_map, Category.id_comp]
  rw [ObjectProperty.FullSubcategory.comp_hom]
  rw [NatTrans.comp_app, openAdjunction_unit_app_hom_app]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [pushforward_comp_obj_obj_map]
  rw [pushforward_map_hom_app]
  rw [Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [Functor.sheafPushforwardContinuousComp_hom_app_hom_app]
  rw [Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [sheafPushforwardContinuousIso_hom_app_hom_app]
  rw [Iso.symm_hom]
  rw [Functor.sheafPushforwardContinuousComp_inv_app_hom_app]
  rw [pushforward_obj_obj_map]
  rw [pushforward_map_hom_app]
  rw [pushforward_map_hom_app]
  rw [openAdjunction_counit_app_hom_app]
  rw [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  rw [ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  rw [Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [Iso.trans_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  rw [Iso.symm_hom, Iso.refl_inv, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have hEq :
      ((eqToIso (congrArg (TopCat.Sheaf.pushforward (Type v))
        (preimageMap_comp_inclusion f V).symm)).hom.app F).hom.app W = 𝟙 _ := by
    rfl
  rw [hEq]
  simp only [Category.id_comp]
  change F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _ = 𝟙 _
  rw [← Functor.map_comp, ← Functor.map_comp, ← F.obj.map_id]
  congr 1

private theorem baseChangeSquare_eq_whisker {X Y : TopCat.{v}}
    (f : X ⟶ Y) (V : Opens Y) :
    baseChangeSquare f V =
      ((naiveBaseChangeSquare f V).whiskerRight
          (comparison V.isOpenEmbedding).hom).whiskerLeft
        (comparison ((Opens.map f).obj V).isOpenEmbedding).inv := by
  rfl

private theorem baseChangeSquare_mate_open {X Y : TopCat.{v}}
    (f : X ⟶ Y) (V : Opens Y) :
    CategoryTheory.mateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        ((Opens.map f).obj V).inclusion')
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion')
      (baseChangeSquare f V) = pushforwardSquare f V := by
  rw [baseChangeSquare_eq_whisker,
    conjugateEquiv_mateEquiv_vcomp,
    mateEquiv_conjugateEquiv_vcomp,
    naiveBaseChangeSquare_mate]
  simp [comparison, CategoryTheory.Adjunction.leftAdjointUniq,
    TwoSquare.whiskerBottom, TwoSquare.whiskerTop]

private theorem pullbackSquare_conjugate {X Y : TopCat.{v}}
    (f : X ⟶ Y) (V : Opens Y) :
    CategoryTheory.conjugateEquiv
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).comp
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
          ((Opens.map f).obj V).inclusion'))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion').comp
        (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
          (preimageMap f V)))
      (pullbackSquare f V) = pushforwardSquare f V := by
  have hPullbackComp
      {sourceSpace middleSpace targetSpace : TopCat.{v}}
      (firstMap : sourceSpace ⟶ middleSpace)
      (secondMap : middleSpace ⟶ targetSpace) :
      TopCat.Sheaf.pullbackCompIso (Type v) firstMap secondMap =
        CategoryTheory.Adjunction.leftAdjointCompIso
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) secondMap)
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) firstMap)
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (firstMap ≫ secondMap))
          (pushforwardCompIso firstMap secondMap) := rfl
  simp [pullbackSquare, pullbackSquareIso, pushforwardSquare,
    pushforwardSquareIso, hPullbackComp]
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        ((Opens.map f).obj V).inclusion'))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (((Opens.map f).obj V).inclusion' ≫ f))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion').comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (preimageMap f V)))]
  rw [← conjugateEquiv_comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (((Opens.map f).obj V).inclusion' ≫ f))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (preimageMap f V ≫ V.inclusion'))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion').comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (preimageMap f V)))]
  simp
  rw [← conjugateEquiv_comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (((Opens.map f).obj V).inclusion' ≫ f))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (preimageMap f V ≫ V.inclusion'))
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion').comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (preimageMap f V)))]
  simp [CategoryTheory.Adjunction.leftAdjointCompIso]
  rw [conjugateEquiv_pullback_eqToHom
    (preimageMap_comp_inclusion f V).symm]

/-- The mate of the geometric inverse-image square is direct-image base change. -/
theorem pullbackSquare_mate {X Y : TopCat.{v}}
    (f : X ⟶ Y) (V : Opens Y) :
    CategoryTheory.mateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (preimageMap f V))
      (pullbackSquare f V) = baseChangeSquare f V := by
  apply (CategoryTheory.mateEquiv
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      ((Opens.map f).obj V).inclusion')
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      V.inclusion')).injective
  change ((CategoryTheory.mateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        ((Opens.map f).obj V).inclusion')
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion'))
        ((CategoryTheory.mateEquiv
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
          (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (preimageMap f V))) (pullbackSquare f V))).natTrans =
    ((CategoryTheory.mateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        ((Opens.map f).obj V).inclusion')
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) V.inclusion'))
        (baseChangeSquare f V)).natTrans
  rw [CategoryTheory.iterated_mateEquiv_conjugateEquiv,
    pullbackSquare_conjugate, baseChangeSquare_mate_open]

/-- The inverse mate of direct-image open base change is the geometric square. -/
theorem baseChangeSquare_inv_mate {X Y : TopCat.{v}}
    (f : X ⟶ Y) (V : Opens Y) :
    (CategoryTheory.mateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (preimageMap f V))).symm
      (baseChangeSquare f V) = pullbackSquare f V := by
  apply (CategoryTheory.mateEquiv
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (preimageMap f V))).injective
  rw [Equiv.apply_symm_apply, pullbackSquare_mate]

/-- The mate identification as the literal counit/naturality equation. -/
theorem baseChangeIso_hom_app_comp_counit
    {X Y : TopCat.{v}} (f : X ⟶ Y) (V : Opens Y)
    (F : X.Sheaf (Type v)) :
    (TopCat.Sheaf.pullback (Type v) (preimageMap f V)).map
        ((baseChangeIso f V).hom.app F) ≫
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (preimageMap f V)).counit.app
          ((TopCat.Sheaf.pullback (Type v)
            ((Opens.map f).obj V).inclusion').obj F) =
    (pullbackSquareIso f V).hom.app
        ((TopCat.Sheaf.pushforward (Type v) f).obj F) ≫
      (TopCat.Sheaf.pullback (Type v)
        ((Opens.map f).obj V).inclusion').map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).counit.app F) := by
  have h := CategoryTheory.mateEquiv_counit_symm
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (preimageMap f V))
    (baseChangeSquare f V) F
  rw [baseChangeSquare_inv_mate] at h
  exact h

#print axioms baseChangeIso_eq_privateConstruction

end TopCat.Sheaf.OpenBaseChange
