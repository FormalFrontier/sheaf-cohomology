/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier worker-b Hive Task hive-request-e5e544a630e9b84215130384682791cdebd0aea0
-/
module
public import SheafCohomology.NativeStageSectionEquality
public import SheafCohomology.ConePullbackSections
public import SpectralStoneDuality.FiniteCylinderDescent
public import SpectralStoneDuality.Limits

public section

set_option warningAsError true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Native lifting of sections to a filtered stage

A section of the actual cone pullback of a filtered diagram of spectral sheafed
spaces comes from a global section at some later native stage. No point of the
limit, or of any stage, is assumed to exist.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopologicalSpace.Opens

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))

include hc hstage htransition

omit [IsFiltered J] in
private theorem compactSpace_conePoint : CompactSpace c.pt := by
  let e := TopCat.homeoOfIso (hc.conePointUniqueUpToIso
    (TopCat.limitConeIsLimit (N ⋙ SheafedSpace.forget (Type v))))
  letI := SpectralStoneDuality.compactSpace_limit_of_spectral
    (N ⋙ SheafedSpace.forget (Type v)) hstage htransition
  exact e.symm.compactSpace

private theorem prespectralSpace_conePoint : PrespectralSpace c.pt := by
  let e := TopCat.homeoOfIso (hc.conePointUniqueUpToIso
    (TopCat.limitConeIsLimit (N ⋙ SheafedSpace.forget (Type v))))
  letI := SpectralStoneDuality.prespectralSpace_limit_of_spectral
    (N ⋙ SheafedSpace.forget (Type v)) hstage htransition
  exact e.isOpenEmbedding.prespectralSpace

private theorem finite_stage_eq_of_pullback_unit_eq
    {α : Type v} [Finite α] (i : J)
    (V : α → Opens (N.obj (op i)))
    (hV : ∀ p, IsCompact (V p : Set (N.obj (op i))))
    (a b : ∀ p, (N.obj (op i)).presheaf.obj (op (V p)))
    (heq : ∀ p,
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V p)) (a p) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V p)) (b p)) :
    ∃ (j : J) (g : i ⟶ j), ∀ p,
      (N.map g.op).hom.c.app (op (V p)) (a p) =
      (N.map g.op).hom.c.app (op (V p)) (b p) := by
  classical
  choose stage arrow equality using fun p =>
    exists_stage_eq_of_pullback_unit_eq N c hc hstage htransition
      i (V p) (hV p) (a p) (b p) (heq p)
  obtain ⟨j, g, next, hcomm⟩ := IsFiltered.wideSpan arrow
  refine ⟨j, g, ?_⟩
  intro p
  have transferred := congrArg
    ((N.map (next p).op).hom.c.app
      (op ((Opens.map (N.map (arrow p).op).hom.base).obj (V p)))) (equality p)
  rw [← hcomm p, op_comp, N.map_comp]
  exact transferred

omit [IsFiltered J] hc hstage htransition in
private theorem map_restrict {i j : J} (g : i ⟶ j)
    {U V : Opens (N.obj (op i))} (h : V ≤ U)
    (hmap : (Opens.map (N.map g.op).hom.base).obj V ≤
      (Opens.map (N.map g.op).hom.base).obj U)
    (s : (N.obj (op i)).presheaf.obj (op U)) :
    (N.obj (op j)).presheaf.map
        (homOfLE hmap).op
        ((N.map g.op).hom.c.app (op U) s) =
      (N.map g.op).hom.c.app (op V)
        ((N.obj (op i)).presheaf.map (homOfLE h).op s) := by
  have hn := (N.map g.op).hom.c.naturality (homOfLE h).op
  change (N.obj (op i)).presheaf.map (homOfLE h).op ≫
      (N.map g.op).hom.c.app (op V) =
    (N.map g.op).hom.c.app (op U) ≫
      (N.obj (op j)).presheaf.map
      (homOfLE hmap).op at hn
  exact (ConcreteCategory.congr_hom hn s).symm

private theorem exists_native_global_gluing_of_unit_compatible_cover
    {α : Type v} [Finite α] (i : J)
    (V : α → Opens (N.obj (op i)))
    (hV : ∀ a, IsCompact (V a : Set (N.obj (op i))))
    (hCover : (⨆ a, V a) = ⊤)
    (s : ∀ a, (N.obj (op i)).presheaf.obj (op (V a)))
    (hUnit : ∀ a b,
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a ⊓ V b))
        ((N.obj (op i)).presheaf.map (infLELeft (V a) (V b)).op (s a)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a ⊓ V b))
        ((N.obj (op i)).presheaf.map (infLERight (V a) (V b)).op (s b))) :
    ∃ (j : J) (g : i ⟶ j)
      (t : (N.obj (op j)).presheaf.obj (op (⊤ : Opens (N.obj (op j))))),
      ∀ a,
        let B : Opens (N.obj (op j)) := (Opens.map (N.map g.op).hom.base).obj (V a)
        (N.obj (op j)).presheaf.map (homOfLE (le_top : B ≤ ⊤)).op t =
          (N.map g.op).hom.c.app (op (V a)) (s a) := by
  classical
  letI : SpectralSpace (N.obj (op i)) := hstage (op i)
  let W : α × α → Opens (N.obj (op i)) := fun pair => V pair.1 ⊓ V pair.2
  let left : (pair : α × α) → (N.obj (op i)).presheaf.obj (op (W pair)) :=
    fun pair => (N.obj (op i)).presheaf.map
      (infLELeft (V pair.1) (V pair.2)).op (s pair.1)
  let right : (pair : α × α) → (N.obj (op i)).presheaf.obj (op (W pair)) :=
    fun pair => (N.obj (op i)).presheaf.map
      (infLERight (V pair.1) (V pair.2)).op (s pair.2)
  have hW (pair : α × α) : IsCompact (W pair : Set (N.obj (op i))) :=
    (hV pair.1).inter_of_isOpen (hV pair.2) (V pair.1).isOpen (V pair.2).isOpen
  obtain ⟨j, g, hpair⟩ := finite_stage_eq_of_pullback_unit_eq
    N c hc hstage htransition i W hW left right (fun pair => hUnit pair.1 pair.2)
  let B : α → Opens (N.obj (op j)) := fun a => (Opens.map (N.map g.op).hom.base).obj (V a)
  let tloc : (a : α) → (N.obj (op j)).presheaf.obj (op (B a)) :=
    fun a => (N.map g.op).hom.c.app (op (V a)) (s a)
  have hB (a b : α) : B a ⊓ B b =
      (Opens.map (N.map g.op).hom.base).obj (V a ⊓ V b) := by
    ext x
    rfl
  have compatible : TopCat.Presheaf.IsCompatible
      (N.obj (op j)).sheaf.1 B tloc := by
    intro a b
    have hleft := map_restrict N g (inf_le_left : V a ⊓ V b ≤ V a)
      (show (Opens.map (N.map g.op).hom.base).obj (V a ⊓ V b) ≤ B a from
        fun _ hx => hx.1) (s a)
    have hright := map_restrict N g (inf_le_right : V a ⊓ V b ≤ V b)
      (show (Opens.map (N.map g.op).hom.base).obj (V a ⊓ V b) ≤ B b from
        fun _ hx => hx.2) (s b)
    have hs := hpair (a, b)
    dsimp only [W, left, right] at hs
    change (N.obj (op j)).presheaf.map
        (homOfLE (Opens.comap_mono (N.map g.op).hom.base.hom
          (inf_le_left : V a ⊓ V b ≤ V a))).op
        ((N.map g.op).hom.c.app (op (V a)) (s a)) =
      (N.obj (op j)).presheaf.map
        (homOfLE (Opens.comap_mono (N.map g.op).hom.base.hom
          (inf_le_right : V a ⊓ V b ≤ V b))).op
        ((N.map g.op).hom.c.app (op (V b)) (s b))
    exact hleft.trans (hs.trans hright.symm)
  have hStageCover : (⨆ a, B a) = ⊤ := by
    have total : (Opens.map (N.map g.op).hom.base).obj (⨆ a, V a) = ⊤ := by
      rw [hCover, Opens.map_top]
    simpa only [Opens.map_iSup, Function.comp_def, B] using total
  obtain ⟨t, ht, _⟩ := (N.obj (op j)).sheaf.existsUnique_gluing'
    B ⊤ (fun a => homOfLE le_top) (le_of_eq hStageCover.symm) tloc compatible
  exact ⟨j, g, t, ht⟩

omit [IsFiltered J] hc hstage htransition in
private theorem restrictedAdjoint_sheafMate {i j : J} (g : i ⟶ j)
    (U : Opens (N.obj (op i))) (V : Opens (N.obj (op j)))
    (hV : V ≤ (Opens.map (N.map g.op).hom.base).obj U) :
    SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap
      (N.map g.op).hom.base (SheafedSpace.sheafMate (Type v) (N.map g.op)) U V hV =
      (N.map g.op).hom.c.app (op U) ≫
        (N.obj (op j)).presheaf.map (homOfLE hV).op := by
  let f := (N.map g.op).hom.base
  let mate := SheafedSpace.sheafMate (Type v) (N.map g.op)
  have hunit := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv_unit
    (f := mate)
  have hmate := SheafedSpace.sheafMate_adjoint (Type v) (N.map g.op)
  have hraw := congrArg (fun m => m.hom.app (op U)) (hunit.symm.trans hmate)
  change (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app
    (N.obj (op i)).sheaf).hom.app (op U)) ≫
      mate.hom.app (op ((Opens.map f).obj U)) =
    (N.map g.op).hom.c.app (op U) at hraw
  have hnat := mate.hom.naturality (homOfLE hV).op
  change ((TopCat.Sheaf.pullback (Type v) f).obj (N.obj (op i)).sheaf).1.map
      (homOfLE hV).op ≫ mate.hom.app (op V) =
    mate.hom.app (op ((Opens.map f).obj U)) ≫
      (N.obj (op j)).presheaf.map (homOfLE hV).op at hnat
  calc
    _ = SheafCohomology.ConePullbackSections.restrictedUnitSectionMap
        f (N.obj (op i)).sheaf U V hV ≫ mate.hom.app (op V) :=
        SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap_eq_unit_comp
          f mate U V hV
    _ = (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app
        (N.obj (op i)).sheaf).hom.app (op U) ≫
          ((TopCat.Sheaf.pullback (Type v) f).obj (N.obj (op i)).sheaf).1.map
            (homOfLE hV).op) ≫ mate.hom.app (op V) := by
          rw [SheafCohomology.ConePullbackSections.restrictedUnitSectionMap_eq_unit_comp]
    _ = (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app
        (N.obj (op i)).sheaf).hom.app (op U) ≫
          mate.hom.app (op ((Opens.map f).obj U))) ≫
            (N.obj (op j)).presheaf.map (homOfLE hV).op := by
          simp only [Category.assoc, hnat]
    _ = _ := by
      rw [hraw]

omit [IsFiltered J] hc hstage htransition in
private theorem transported_local_unit {i j : J} (g : i ⟶ j)
    (A : Opens (N.obj (op i))) (V : Opens (N.obj (op j)))
    (hV : V ≤ (Opens.map (N.map g.op).hom.base).obj A)
    (a : (N.obj (op i)).presheaf.obj (op A))
    (s : ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
      (N.obj (op i)).sheaf).1.obj (op (⊤ : Opens c.pt)))
    (hRep :
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (SheafCohomology.ConePullbackSections.triangleOpen_le
            (N.map g.op).hom.base (c.w g.op) hV le_rfl)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op A) a) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (le_top :
            (Opens.map (c.π.app (op j))).obj V ≤ ⊤)).op s) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
      (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app (op V)
        ((N.obj (op j)).presheaf.map (homOfLE hV).op
          ((N.map g.op).hom.c.app (op A) a)) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op j))).obj
        (N.obj (op j)).sheaf).1.map
          (homOfLE (le_top :
            (Opens.map (c.π.app (op j))).obj V ≤ ⊤)).op
          ((SheafedSpace.conePullback (Type v) N c ⋙
            SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s) := by
  classical
  let f := (N.map g.op).hom.base
  let p := c.π.app (op i)
  let q := c.π.app (op j)
  let mate := SheafedSpace.sheafMate (Type v) (N.map g.op)
  have htriangle := SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap_triangle
    f (c.w g.op) mate A V ((Opens.map q).obj V) hV le_rfl
  have hfactor := SheafCohomology.ConePullbackSections.restrictedAdjointSectionMap_eq_unit_comp
    p (SheafedSpace.triangleMap (Type v) (c.w g.op) mate)
    A ((Opens.map q).obj V)
    (SheafCohomology.ConePullbackSections.triangleOpen_le f (c.w g.op) hV le_rfl)
  have hnaturality := (SheafedSpace.conePullbackMap (Type v) N c g).hom.naturality
    (homOfLE (le_top : (Opens.map q).obj V ≤ ⊤)).op
  have hTopMap : (SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g =
        (SheafedSpace.conePullbackMap (Type v) N c g).hom.app
          (op (⊤ : Opens c.pt)) := by rfl
  rw [hfactor] at htriangle
  rw [restrictedAdjoint_sheafMate N g A V hV] at htriangle
  simp only [SheafCohomology.ConePullbackSections.restrictedUnitSectionMap_eq_unit_comp]
    at htriangle
  have hpoint := ConcreteCategory.congr_hom htriangle a
  have hnatpoint := ConcreteCategory.congr_hom hnaturality s
  have hId : (((TopCat.Sheaf.pullback (Type v) q).obj
      (N.obj (op j)).sheaf).1.map
        (homOfLE (le_rfl : (Opens.map q).obj V ≤ (Opens.map q).obj V)).op) =
      𝟙 _ := by simp
  rw [hId] at hpoint
  simp only [ConcreteCategory.comp_apply] at hpoint
  have hpoint' := hpoint.symm
  change (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) q).unit.app
      (N.obj (op j)).sheaf).hom.app (op V))
        (((N.obj (op j)).presheaf.map (homOfLE hV).op)
          ((N.map g.op).hom.c.app (op A) a)) =
    (SheafedSpace.conePullbackMap (Type v) N c g).hom.app
      (op ((Opens.map q).obj V))
        (((TopCat.Sheaf.pullback (Type v) p).obj (N.obj (op i)).sheaf).1.map
          (homOfLE (SheafCohomology.ConePullbackSections.triangleOpen_le
            f (c.w g.op) hV le_rfl)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) p).unit.app
            (N.obj (op i)).sheaf).hom.app (op A) a)) at hpoint'
  calc
    _ = (SheafedSpace.conePullbackMap (Type v) N c g).hom.app
        (op ((Opens.map q).obj V))
        (((TopCat.Sheaf.pullback (Type v) p).obj (N.obj (op i)).sheaf).1.map
          (homOfLE (SheafCohomology.ConePullbackSections.triangleOpen_le
            f (c.w g.op) hV le_rfl)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) p).unit.app
            (N.obj (op i)).sheaf).hom.app (op A) a)) := by
          exact hpoint'
    _ = (SheafedSpace.conePullbackMap (Type v) N c g).hom.app
        (op ((Opens.map q).obj V))
        (((TopCat.Sheaf.pullback (Type v) p).obj (N.obj (op i)).sheaf).1.map
          (homOfLE (le_top : (Opens.map q).obj V ≤ ⊤)).op s) := by
          exact congrArg _ hRep
    _ = _ := by
      rw [hTopMap]
      convert hnatpoint using 1 <;> rfl

omit [IsFiltered J] hc hstage htransition in
private theorem unit_restrict {X Y : TopCat.{v}} (f : X ⟶ Y) (F : Y.Sheaf (Type v))
    {U V : Opens Y} (h : V ≤ U)
    (hmap : (Opens.map f).obj V ≤ (Opens.map f).obj U)
    (s : F.1.obj (op U)) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
        (op V) (F.1.map (homOfLE h).op s) =
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hmap).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
          (op U) s) := by
  have hnat := ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.naturality
    (homOfLE h).op
  change F.1.map (homOfLE h).op ≫
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
        (op V) =
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
        (op U) ≫
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hmap).op at hnat
  exact ConcreteCategory.congr_hom hnat s

omit [IsFiltered J] hc hstage htransition in
private theorem restrict_restrict {X : TopCat.{v}} (F : X.Sheaf (Type v))
    {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V) (s : F.1.obj (op U)) :
    F.1.map (homOfLE hWV).op (F.1.map (homOfLE hVU).op s) =
      F.1.map (homOfLE (hWV.trans hVU)).op s := by
  rw [← ConcreteCategory.comp_apply, ← F.1.map_comp]
  exact ConcreteCategory.congr_hom (congrArg F.1.map (Subsingleton.elim _ _)) s

private theorem exists_stage_lift_of_local_cover {α : Type v} [Finite α] (i : J)
    (V : α → Opens (N.obj (op i)))
    (hV : ∀ a, IsCompact (V a : Set (N.obj (op i))))
    (hCover : (⨆ a, V a) = ⊤)
    (b : ∀ a, (N.obj (op i)).presheaf.obj (op (V a)))
    (s : (SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).obj i)
    (hLocal : ∀ a,
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a)) (b a) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (le_top :
            (Opens.map (c.π.app (op i))).obj (V a) ≤ ⊤)).op s) :
    ∃ (j : J) (g : i ⟶ j) (t : (N.rightOp ⋙ SheafedSpace.Γ).obj j),
      (SheafCohomology.ConePullbackSections.coneSections N c).app j t =
        (SheafedSpace.conePullback (Type v) N c ⋙
          SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s := by
  classical
  have hUnit (a d : α) :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a ⊓ V d))
          ((N.obj (op i)).presheaf.map (infLELeft (V a) (V d)).op (b a)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a ⊓ V d))
          ((N.obj (op i)).presheaf.map (infLERight (V a) (V d)).op (b d)) := by
    let F := (TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
      (N.obj (op i)).sheaf
    have hLeft : (Opens.map (c.π.app (op i))).obj (V a ⊓ V d) ≤
        (Opens.map (c.π.app (op i))).obj (V a) := fun _ hx => hx.1
    have hRight : (Opens.map (c.π.app (op i))).obj (V a ⊓ V d) ≤
        (Opens.map (c.π.app (op i))).obj (V d) := fun _ hx => hx.2
    have eqLeft :
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
          (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a ⊓ V d))
            ((N.obj (op i)).presheaf.map (infLELeft (V a) (V d)).op (b a)) =
        F.1.map (homOfLE (le_top :
          (Opens.map (c.π.app (op i))).obj (V a ⊓ V d) ≤ ⊤)).op s := by
      calc
        _ = F.1.map (homOfLE hLeft).op
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
              (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
                (op (V a)) (b a)) :=
              unit_restrict (c.π.app (op i)) (N.obj (op i)).sheaf
                (inf_le_left : V a ⊓ V d ≤ V a) hLeft (b a)
        _ = F.1.map (homOfLE hLeft).op
            (F.1.map (homOfLE (le_top :
              (Opens.map (c.π.app (op i))).obj (V a) ≤ ⊤)).op s) :=
              congrArg _ (hLocal a)
        _ = _ := restrict_restrict F le_top hLeft s
    have eqRight :
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
          (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a ⊓ V d))
            ((N.obj (op i)).presheaf.map (infLERight (V a) (V d)).op (b d)) =
        F.1.map (homOfLE (le_top :
          (Opens.map (c.π.app (op i))).obj (V a ⊓ V d) ≤ ⊤)).op s := by
      calc
        _ = F.1.map (homOfLE hRight).op
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
              (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
                (op (V d)) (b d)) :=
              unit_restrict (c.π.app (op i)) (N.obj (op i)).sheaf
                (inf_le_right : V a ⊓ V d ≤ V d) hRight (b d)
        _ = F.1.map (homOfLE hRight).op
            (F.1.map (homOfLE (le_top :
              (Opens.map (c.π.app (op i))).obj (V d) ≤ ⊤)).op s) :=
              congrArg _ (hLocal d)
        _ = _ := restrict_restrict F le_top hRight s
    exact eqLeft.trans eqRight.symm
  obtain ⟨j, g, t, ht⟩ := exists_native_global_gluing_of_unit_compatible_cover
    N c hc hstage htransition i V hV hCover b hUnit
  let B : α → Opens (N.obj (op j)) :=
    fun a => (Opens.map (N.map g.op).hom.base).obj (V a)
  let Q : α → Opens c.pt := fun a => (Opens.map (c.π.app (op j))).obj (B a)
  have hStageCover : (⨆ a, B a) = ⊤ := by
    have total : (Opens.map (N.map g.op).hom.base).obj (⨆ a, V a) = ⊤ := by
      rw [hCover, Opens.map_top]
    simpa only [Opens.map_iSup, Function.comp_def, B] using total
  have hConeCover : (⨆ a, Q a) = ⊤ := by
    have total : (Opens.map (c.π.app (op j))).obj (⨆ a, B a) = ⊤ := by
      rw [hStageCover, Opens.map_top]
    simpa only [Opens.map_iSup, Function.comp_def, Q] using total
  have hOp (a : α) : Q a = (Opens.map (c.π.app (op i))).obj (V a) := by
    have hw : c.π.app (op j) ≫ (N.map g.op).hom.base =
        c.π.app (op i) := c.w g.op
    calc
      Q a = (Opens.map (c.π.app (op j) ≫ (N.map g.op).hom.base)).obj (V a) := by
        simpa only [Q, B] using
          (Opens.map_comp_obj (c.π.app (op j)) (N.map g.op).hom.base (V a)).symm
      _ = _ := by rw [hw]
  have hRep (a : α) :
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (SheafCohomology.ConePullbackSections.triangleOpen_le
            (N.map g.op).hom.base (c.w g.op)
            (le_rfl : B a ≤ (Opens.map (N.map g.op).hom.base).obj (V a)) le_rfl)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op (V a)) (b a)) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (le_top : Q a ≤ ⊤)).op s := by
    let F := (TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
      (N.obj (op i)).sheaf
    have hQ : Q a ≤ (Opens.map (c.π.app (op i))).obj (V a) := le_of_eq (hOp a)
    calc
      _ = F.1.map (homOfLE hQ).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
              (op (V a)) (b a)) := by rfl
      _ = F.1.map (homOfLE hQ).op
          (F.1.map (homOfLE (le_top :
            (Opens.map (c.π.app (op i))).obj (V a) ≤ ⊤)).op s) :=
              congrArg _ (hLocal a)
      _ = _ := restrict_restrict F le_top hQ s
  have hPatch (a : α) :
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op j))).obj
        (N.obj (op j)).sheaf).1.map (homOfLE (le_top : Q a ≤ ⊤)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app
              (op (⊤ : Opens (N.obj (op j)))) t) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op j))).obj
        (N.obj (op j)).sheaf).1.map (homOfLE (le_top : Q a ≤ ⊤)).op
          ((SheafedSpace.conePullback (Type v) N c ⋙
            SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s) := by
    have hTransport := transported_local_unit N c g (V a) (B a) le_rfl (b a) s (hRep a)
    have hId : (N.obj (op j)).presheaf.map
        (homOfLE (le_rfl : B a ≤ B a)).op = 𝟙 _ := by simp
    rw [hId] at hTransport
    calc
      _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app (op (B a))
          ((N.obj (op j)).presheaf.map (homOfLE le_top).op t) := by
            exact (unit_restrict (c.π.app (op j)) (N.obj (op j)).sheaf
              (le_top : B a ≤ ⊤) (le_top : Q a ≤ ⊤) t).symm
      _ = ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app (op (B a))
          ((N.map g.op).hom.c.app (op (V a)) (b a)) := by
            exact congrArg _ (ht a)
      _ = _ := hTransport
  have hEq :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app
          (op (⊤ : Opens (N.obj (op j)))) t =
      (SheafedSpace.conePullback (Type v) N c ⋙
        SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s := by
    apply ((SheafedSpace.conePullback (Type v) N c).obj j).eq_of_locally_eq'
      Q ⊤ (fun a => homOfLE le_top) (le_of_eq hConeCover.symm)
    exact hPatch
  exact ⟨j, g, t, hEq⟩

include hc hstage htransition in
/-- Every section of the actual pullback cone at a stage lifts from a native
global section after one filtered transition. The conclusion uses the literal
projection unit and the actual transition of the cone pullback. -/
theorem exists_native_stage_section_lift (i : J)
    (s : (SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).obj i) :
    ∃ (j : J) (g : i ⟶ j) (a : (N.rightOp ⋙ SheafedSpace.Γ).obj j),
      (SheafCohomology.ConePullbackSections.coneSections N c).app j a =
        (SheafedSpace.conePullback (Type v) N c ⋙
          SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s := by
  classical
  letI : CompactSpace c.pt := compactSpace_conePoint N c hc hstage htransition
  letI : PrespectralSpace c.pt := prespectralSpace_conePoint N c hc hstage htransition
  have htop : IsCompact ((⊤ : Opens c.pt) : Set c.pt) := isCompact_univ
  obtain ⟨G, W, A, a, hWU, hWA, hFull, hData⟩ :=
    TopCat.Sheaf.PullbackLocalSections.exists_finite_compact_representation
      (X := c.pt) (U := ⊤) (c.π.app (op i)) (N.obj (op i)).sheaf htop s
  let α := {x : (⊤ : Opens c.pt) // x ∈ G}
  have hWcover : (⨆ label : α, W label) = ⊤ := by
    apply top_unique
    intro x _
    have hx := hFull (show x ∈ (⊤ : Set c.pt) by trivial)
    rcases Set.mem_iUnion.mp hx with ⟨label, hlabel⟩
    exact Opens.mem_iSup.mpr ⟨label, hlabel⟩
  have hWcompact (label : α) : IsCompact (W label : Set c.pt) := (hData label).1
  obtain ⟨X, V, hV, hStageCover, hWV, hVA⟩ :=
    SpectralStoneDuality.exists_finiteCompactOpen_fullStageCover
      (N ⋙ SheafedSpace.forget (Type v)) c hc hstage htransition
      (op i) W A hWcompact hWcover hWA
  rcases X with ⟨stage, ⟨⟩, arrow⟩
  rcases stage with ⟨j⟩
  change α → Opens (N.obj (op j)) at V
  change ∀ label : α, W label =
    (Opens.map (c.π.app (op j))).obj (V label) at hWV
  change ∀ label : α, V label ≤
    (Opens.map (N.map arrow).hom.base).obj (A label) at hVA
  let g : i ⟶ j := arrow.unop
  have hV' (label : α) : IsCompact (V label : Set (N.obj (op j))) := by
    exact hV label
  have hVA' (label : α) : V label ≤
      (Opens.map (N.map g.op).hom.base).obj (A label) := by
    simpa only [g, Quiver.Hom.op_unop, Functor.comp_map] using hVA label
  let b (label : α) : (N.obj (op j)).presheaf.obj (op (V label)) :=
    (N.obj (op j)).presheaf.map (homOfLE (hVA' label)).op
      ((N.map g.op).hom.c.app (op (A label)) (a label))
  have hRep (label : α) :
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (SheafCohomology.ConePullbackSections.triangleOpen_le
            (N.map g.op).hom.base (c.w g.op) (hVA' label) le_rfl)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
              (op (A label)) (a label)) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (le_top :
            (Opens.map (c.π.app (op j))).obj (V label) ≤ ⊤)).op s := by
    let F := (TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
      (N.obj (op i)).sheaf
    have hW : (Opens.map (c.π.app (op j))).obj (V label) ≤ W label :=
      le_of_eq (hWV label).symm
    calc
      _ = F.1.map (homOfLE hW).op
          (F.1.map (homOfLE (hWA label)).op
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
              (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
                (op (A label)) (a label))) := by
          exact (restrict_restrict F (hWA label) hW _).symm
      _ = F.1.map (homOfLE hW).op
          (F.1.map (homOfLE (hWU label)).op s) :=
            congrArg _ (hData label).2
      _ = _ := restrict_restrict F (hWU label) hW s
  have hLocal (label : α) :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op j))).unit.app (N.obj (op j)).sheaf).hom.app
          (op (V label)) (b label) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op j))).obj
        (N.obj (op j)).sheaf).1.map
          (homOfLE (le_top :
            (Opens.map (c.π.app (op j))).obj (V label) ≤ ⊤)).op
          ((SheafedSpace.conePullback (Type v) N c ⋙
            SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s) := by
    exact transported_local_unit N c g (A label) (V label) (hVA' label)
      (a label) s (hRep label)
  obtain ⟨k, move, lift, hLift⟩ := exists_stage_lift_of_local_cover
    N c hc hstage htransition j V hV' hStageCover b
    ((SheafedSpace.conePullback (Type v) N c ⋙
      SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s) hLocal
  refine ⟨k, g ≫ move, lift, ?_⟩
  simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hLift

end AlgebraicGeometry.SheafedSpace
