/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents, Anchor (Source Maintainer)
-/
module
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Spectral.Prespectral

public section

set_option warningAsError true

/-!
# Local sections of the actual inverse-image sheaf

The stalk comparison, local representation, equality reflection and compact-open
finite cover all use the chosen `TopCat.Sheaf.pullback` and the unit of its
`pullbackPushforwardAdjunction`. In particular, their sections are not sections
of a different chosen model of inverse image. The proof compares the native
adjunction unit with a left-Kan-extension-and-sheafification construction.
-/


open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe v
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
namespace TopCat.Sheaf.PullbackLocalSections
variable {X Y : TopCat.{v}} (f : X ⟶ Y) (F : Y.Sheaf (Type v))

private def pullbackPresheafMap :
    (TopCat.Presheaf.pullback (Type v) f).obj F.1 ⟶
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1 :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((TopCat.Presheaf.pullback (Type v) f).obj F.1) ≫
    ((TopCat.Sheaf.pullbackIso (Type v) f).inv.app F).hom

private theorem constructed_unit_hom :
    ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) (Type v) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app F).hom =
      ((Opens.map f).op.lanAdjunction (Type v)).unit.app F.1 ≫
        Functor.whiskerLeft (Opens.map f).op
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback (Type v) f).obj F.1)) := by
  change (CategoryTheory.sheafToPresheaf
    (Opens.grothendieckTopology Y) (Type v)).map
      ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map f) (Type v) (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app F) = _
  simp only [CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app, Adjunction.comp_unit_app,
    CategoryTheory.sheafificationAdjunction_unit_app]
  rfl

private theorem native_unit_eq_constructed :
    (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) (Type v) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app F ≫
      (TopCat.Sheaf.pushforward (Type v) f).map
        ((TopCat.Sheaf.pullbackIso (Type v) f).inv.app F) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F := by
  let adjA := TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f
  let adjB :=
    CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map f) (Type v) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)
  rw [← Adjunction.unit_leftAdjointUniq_hom_app adjA adjB F]
  change (adjA.unit.app F ≫
      (TopCat.Sheaf.pushforward (Type v) f).map
        ((TopCat.Sheaf.pullbackIso (Type v) f).hom.app F)) ≫
      (TopCat.Sheaf.pushforward (Type v) f).map
        ((TopCat.Sheaf.pullbackIso (Type v) f).inv.app F) =
    adjA.unit.app F
  rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  change adjA.unit.app F ≫ 𝟙 _ = adjA.unit.app F
  rw [Category.comp_id]

private theorem native_unit_app (V : Opens Y) (a : F.1.obj (op V)) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app (op V) a =
      (pullbackPresheafMap f F).app (op ((Opens.map f).obj V))
        (((TopCat.Presheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F.1).app (op V) a) := by
  calc
    _ = ((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) (Type v) (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app F ≫
        (TopCat.Sheaf.pushforward (Type v) f).map
          ((TopCat.Sheaf.pullbackIso (Type v) f).inv.app F)).hom.app (op V) a :=
      congrArg (fun α : F ⟶ _ ↦ α.hom.app (op V) a)
        (native_unit_eq_constructed f F).symm
    _ = _ := by
      change (((CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) (Type v) (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app F).hom.app (op V) ≫
        (((TopCat.Sheaf.pullbackIso (Type v) f).inv.app F).hom).app
          (op ((Opens.map f).obj V))) a = _
      rw [constructed_unit_hom f F]
      rfl

private def nativeStalkHom (x : X) : F.presheaf.stalk (f x) ⟶
    ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (Type v) (f x)).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom ≫
      ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.stalkPushforward (Type v) f x

private theorem nativeStalkHom_eq (x : X) :
    nativeStalkHom f F x = (TopCat.Presheaf.stalkPullbackIso (Type v) f F.1 x).hom ≫
      (TopCat.Presheaf.stalkFunctor (Type v) x).map (pullbackPresheafMap f F) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro V hxV
  ext a
  simpa [nativeStalkHom, TopCat.Presheaf.stalkPullbackIso,
    TopCat.Presheaf.stalkFunctor_map_germ_apply,
    TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.germ_stalkPullbackHom] using
    congrArg (fun t ↦ ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
      ((Opens.map f).obj V) x hxV t) (native_unit_app f F V a)

private instance pullbackPresheafMap_stalk_isIso (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map
      (pullbackPresheafMap f F)) := by
  unfold pullbackPresheafMap
  rw [Functor.map_comp]
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type v)
    ((TopCat.Presheaf.pullback (Type v) f).obj F.1)
  letI : IsIso (((TopCat.Sheaf.pullbackIso (Type v) f).inv.app F).hom) := by
    change IsIso ((TopCat.Sheaf.forget (Type v) X).map
      ((TopCat.Sheaf.pullbackIso (Type v) f).inv.app F))
    infer_instance
  infer_instance

private instance nativeStalkHom_isIso (x : X) : IsIso (nativeStalkHom f F x) := by
  rw [nativeStalkHom_eq]
  letI : IsIso ((TopCat.Presheaf.stalkPullbackIso (Type v) f F.1 x).hom) :=
    (TopCat.Presheaf.stalkPullbackIso (Type v) f F.1 x).isIso_hom
  letI : IsIso ((TopCat.Presheaf.stalkFunctor (Type v) x).map
      (pullbackPresheafMap f F)) := pullbackPresheafMap_stalk_isIso f F x
  infer_instance

/-- The actual inverse-image sheaf has at `x` the stalk of the original sheaf at `f x`. -/
def stalkIso (x : X) : F.presheaf.stalk (f x) ≅
    ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.stalk x :=
  asIso (nativeStalkHom f F x)

/-- The map on germs induced by the actual sheaf-adjunction unit. -/
theorem germ_stalkIso (x : X) (V : Opens Y) (hx : f x ∈ V) :
    F.presheaf.germ V (f x) hx ≫ (stalkIso f F x).hom =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
        (op V) ≫
        ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
          ((Opens.map f).obj V) x hx := by
  simp [stalkIso, nativeStalkHom, TopCat.Presheaf.stalkPushforward_germ]

/-- Locally, a section of the actual inverse-image sheaf comes from a target section
through the actual pullback--pushforward unit. -/
theorem exists_local_representation {U : Opens X}
    (s : ((TopCat.Sheaf.pullback (Type v) f).obj F).1.obj (op U))
    {x : X} (hx : x ∈ U) :
    ∃ (V : Opens Y) (W : Opens X) (_hfx : f x ∈ V) (_hxW : x ∈ W)
      (hWU : W ≤ U) (hWV : W ≤ (Opens.map f).obj V)
      (a : F.1.obj (op V)),
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hWV).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
          (op V) a) =
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hWU).op s := by
  let P := (TopCat.Sheaf.pullback (Type v) f).obj F
  let t := (stalkIso f F x).inv (P.presheaf.germ U x hx s)
  obtain ⟨V, hfx, a, ha⟩ := F.presheaf.exists_germ_eq t
  have hGerm : P.presheaf.germ ((Opens.map f).obj V) x hfx
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
          (op V) a) = P.presheaf.germ U x hx s := by
    calc
      _ = (stalkIso f F x).hom (F.presheaf.germ V (f x) hfx a) := by
        rw [← ConcreteCategory.comp_apply, germ_stalkIso]
        rfl
      _ = _ := by rw [ha]; exact Iso.inv_hom_id_apply _ _
  obtain ⟨W, hxW, iWV, iWU, hres⟩ :=
    P.presheaf.germ_eq x hfx hx
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
        (op V) a) s hGerm
  exact ⟨V, W, hfx, hxW, iWU.le, iWV.le, a, hres⟩

/-- Equality of native-unit sections on an inverse image reflects to one
target neighborhood containing the image of the whole source open. -/
theorem exists_target_eq_neighborhood (V : Opens Y) (U : Opens X)
    (hU : U ≤ (Opens.map f).obj V) (a b : F.1.obj (op V))
    (heq : ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hU).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
          (op V) a) =
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hU).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
          (op V) b)) :
    ∃ (V' : Opens Y) (hV : V' ≤ V),
      U ≤ (Opens.map f).obj V' ∧
        F.1.map (homOfLE hV).op a = F.1.map (homOfLE hV).op b := by
  let P := (TopCat.Sheaf.pullback (Type v) f).obj F
  have hGerm (x : U) :
      F.presheaf.germ V (f x.1) (hU x.2) a =
        F.presheaf.germ V (f x.1) (hU x.2) b := by
    have hPullback :
        P.presheaf.germ ((Opens.map f).obj V) x.1 (hU x.2)
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) a) =
          P.presheaf.germ ((Opens.map f).obj V) x.1 (hU x.2)
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) b) := by
      rw [← P.presheaf.germ_res_apply (homOfLE hU) x.1 x.2,
        ← P.presheaf.germ_res_apply (homOfLE hU) x.1 x.2]
      exact congrArg (P.presheaf.germ U x.1 x.2) heq
    have hIso : (stalkIso f F x.1).hom
          (F.presheaf.germ V (f x.1) (hU x.2) a) =
        (stalkIso f F x.1).hom
          (F.presheaf.germ V (f x.1) (hU x.2) b) := by
      calc
        _ = P.presheaf.germ ((Opens.map f).obj V) x.1 (hU x.2)
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) a) := by
          rw [← ConcreteCategory.comp_apply, germ_stalkIso]
          rfl
        _ = P.presheaf.germ ((Opens.map f).obj V) x.1 (hU x.2)
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) b) := hPullback
        _ = _ := by
          rw [← ConcreteCategory.comp_apply, germ_stalkIso]
          rfl
    have hInv := congrArg (fun t ↦ (stalkIso f F x.1).inv t) hIso
    simpa only [Iso.hom_inv_id_apply] using hInv
  choose W hMem iWa iWb hEq using fun x : U ↦
    F.presheaf.germ_eq (f x.1) (hU x.2) (hU x.2) a b (hGerm x)
  let V' : Opens Y := ⨆ x : U, W x
  have hV : V' ≤ V := iSup_le fun x ↦ (iWa x).le
  have hUV : U ≤ (Opens.map f).obj V' := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hMem ⟨x, hx⟩⟩
  refine ⟨V', hV, hUV, ?_⟩
  apply TopCat.Presheaf.section_ext F V'
  intro y hy
  obtain ⟨x, hyW⟩ := Opens.mem_iSup.mp hy
  have hW : W x ≤ V' := le_iSup W x
  have hRestrict :
      F.1.map (homOfLE hW).op (F.1.map (homOfLE hV).op a) =
      F.1.map (homOfLE hW).op (F.1.map (homOfLE hV).op b) := by
    simp only [← Functor.map_comp_apply]
    convert hEq x using 1
  calc
    F.presheaf.germ V' y hy (F.1.map (homOfLE hV).op a) =
        F.presheaf.germ (W x) y hyW
          (F.1.map (homOfLE hW).op (F.1.map (homOfLE hV).op a)) :=
      (F.presheaf.germ_res_apply (homOfLE hW) y hyW _).symm
    _ = F.presheaf.germ (W x) y hyW
          (F.1.map (homOfLE hW).op (F.1.map (homOfLE hV).op b)) :=
      congrArg _ hRestrict
    _ = F.presheaf.germ V' y hy (F.1.map (homOfLE hV).op b) :=
      F.presheaf.germ_res_apply (homOfLE hW) y hyW _

/-- Compact opens of a prespectral source admit a finite compact-open cover
by restrictions of actual-unit images of target sections. -/
theorem exists_finite_compact_representation [PrespectralSpace X]
    {U : Opens X} (hU : IsCompact (U : Set X))
    (s : ((TopCat.Sheaf.pullback (Type v) f).obj F).1.obj (op U)) :
    ∃ (G : Finset U) (W : {x : U // x ∈ G} → Opens X)
      (V : {x : U // x ∈ G} → Opens Y)
      (a : (i : {x : U // x ∈ G}) → F.1.obj (op (V i)))
      (hWU : ∀ i, W i ≤ U) (hWV : ∀ i, W i ≤ (Opens.map f).obj (V i)),
      (U : Set X) ⊆ ⋃ i, (W i : Set X) ∧
        ∀ i, IsCompact (W i : Set X) ∧
          ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE (hWV i)).op
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op (V i)) (a i)) =
          ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE (hWU i)).op s := by
  classical
  let P := (TopCat.Sheaf.pullback (Type v) f).obj F
  choose V W hfx hxW hWU hWV a hsec using fun x : U ↦
    exists_local_representation f F s x.2
  choose B hB hxB hBW using fun x : U ↦
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open
      (hxW x) (W x).2
  let C (x : U) : Opens X := ⟨B x, (hB x).1⟩
  have hCU (x : U) : C x ≤ U := (hBW x).trans (hWU x)
  have hCV (x : U) : C x ≤ (Opens.map f).obj (V x) :=
    (hBW x).trans (hWV x)
  have hCsec (x : U) :
      P.1.map (homOfLE (hCV x)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
            (op (V x)) (a x)) =
        P.1.map (homOfLE (hCU x)).op s := by
    have e := congrArg
      (P.1.map (homOfLE (show C x ≤ W x from hBW x)).op) (hsec x)
    change
      P.1.map (homOfLE (show C x ≤ W x from hBW x)).op
        (P.1.map (homOfLE (hWV x)).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
            (op (V x)) (a x))) =
      P.1.map (homOfLE (show C x ≤ W x from hBW x)).op
        (P.1.map (homOfLE (hWU x)).op s) at e
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at e
    convert e using 1
  have hcover : (U : Set X) ⊆ ⋃ x : U, (C x : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩
  obtain ⟨G, hG⟩ := hU.elim_finite_subcover
    (fun x : U ↦ (C x : Set X)) (fun x ↦ (C x).2) hcover
  refine ⟨G, (fun i ↦ C i.1), (fun i ↦ V i.1), (fun i ↦ a i.1),
    (fun i ↦ hCU i.1), (fun i ↦ hCV i.1), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hG hx)
    obtain ⟨hiG, hxi⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨⟨i, hiG⟩, hxi⟩
  · intro i
    exact ⟨(hB i.1).2, hCsec i.1⟩

end TopCat.Sheaf.PullbackLocalSections
