/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.PullbackLocalSections

public section

set_option warningAsError true

noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe v

namespace SheafCohomologyExamples.PullbackLocalSections

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (F : Y.Sheaf (Type v))

/-- The actual adjunction unit reflects equality of germs of target sections. -/
theorem native_unit_germ_reflects (V : Opens Y) (x : X) (hx : f x ∈ V)
    (a b : F.1.obj (op V))
    (h : ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
        ((Opens.map f).obj V) x hx
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
            (op V) a) =
      ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
        ((Opens.map f).obj V) x hx
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
            (op V) b)) :
    F.presheaf.germ V (f x) hx a = F.presheaf.germ V (f x) hx b := by
  have hIso :
      (TopCat.Sheaf.PullbackLocalSections.stalkIso f F x).hom
          (F.presheaf.germ V (f x) hx a) =
        (TopCat.Sheaf.PullbackLocalSections.stalkIso f F x).hom
          (F.presheaf.germ V (f x) hx b) := by
    calc
      _ = ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
            ((Opens.map f).obj V) x hx
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) a) := by
        rw [← ConcreteCategory.comp_apply,
          TopCat.Sheaf.PullbackLocalSections.germ_stalkIso]
        rfl
      _ = ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
            ((Opens.map f).obj V) x hx
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) b) := h
      _ = _ := by
        rw [← ConcreteCategory.comp_apply,
          TopCat.Sheaf.PullbackLocalSections.germ_stalkIso]
        rfl
  have hInv := congrArg
    (fun t ↦ (TopCat.Sheaf.PullbackLocalSections.stalkIso f F x).inv t) hIso
  simpa only [Iso.hom_inv_id_apply] using hInv

/-- Every point has a neighborhood on which all germs of the section are
represented by one target section through the actual unit. -/
theorem native_unit_germs_locally_represented {U : Opens X}
    (s : ((TopCat.Sheaf.pullback (Type v) f).obj F).1.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (W : Opens X) (V : Opens Y) (a : F.1.obj (op V))
      (_hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ (Opens.map f).obj V),
      ∀ (y : X) (hy : y ∈ W),
        ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ U y (hWU hy) s =
          ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
            ((Opens.map f).obj V) y (hWV hy)
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) a) := by
  obtain ⟨V, W, _, hxW, hWU, hWV, a, hres⟩ :=
    TopCat.Sheaf.PullbackLocalSections.exists_local_representation f F s hx
  refine ⟨W, V, a, hxW, hWU, hWV, ?_⟩
  intro y hy
  let P := (TopCat.Sheaf.pullback (Type v) f).obj F
  calc
    P.presheaf.germ U y (hWU hy) s =
        P.presheaf.germ W y hy (P.1.map (homOfLE hWU).op s) :=
      (P.presheaf.germ_res_apply (homOfLE hWU) y hy s).symm
    _ = P.presheaf.germ W y hy
          (P.1.map (homOfLE hWV).op
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op V) a)) := congrArg _ hres.symm
    _ = P.presheaf.germ ((Opens.map f).obj V) y (hWV hy)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
            (op V) a) := P.presheaf.germ_res_apply (homOfLE hWV) y hy _

/-- If two target sections have equal native-unit images over an inverse-image
open, they agree after restriction to one target open covering its image. -/
theorem native_equalizer_open (V : Opens Y) (U : Opens X)
    (hU : U ≤ (Opens.map f).obj V) (a b : F.1.obj (op V))
    (h : ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hU).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
          (op V) a) =
      ((TopCat.Sheaf.pullback (Type v) f).obj F).1.map (homOfLE hU).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
          (op V) b)) :
    ∃ V' : Opens Y, U ≤ (Opens.map f).obj V' ∧
      ∃ hV : V' ≤ V, F.1.map (homOfLE hV).op a = F.1.map (homOfLE hV).op b := by
  obtain ⟨V', hV, hUV, heq⟩ :=
    TopCat.Sheaf.PullbackLocalSections.exists_target_eq_neighborhood f F V U hU a b h
  exact ⟨V', hUV, hV, heq⟩

/-- On a compact open, finitely many target sections represent the germs of
every inverse-image section (no compactness is assumed of their target opens). -/
theorem native_finite_target_germ_cover [PrespectralSpace X]
    {U : Opens X} (hU : IsCompact (U : Set X))
    (s : ((TopCat.Sheaf.pullback (Type v) f).obj F).1.obj (op U)) :
    ∃ (G : Finset U) (V : {i : U // i ∈ G} → Opens Y)
      (a : (i : {i : U // i ∈ G}) → F.1.obj (op (V i))),
      ∀ (x : X) (hx : x ∈ U),
        ∃ (i : {i : U // i ∈ G}) (hfx : f x ∈ V i),
          ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ U x hx s =
            ((TopCat.Sheaf.pullback (Type v) f).obj F).presheaf.germ
              ((Opens.map f).obj (V i)) x hfx
              (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
                (op (V i)) (a i)) := by
  classical
  obtain ⟨G, W, V, a, hWU, hWV, hcover, hcomp⟩ :=
    TopCat.Sheaf.PullbackLocalSections.exists_finite_compact_representation f F hU s
  refine ⟨G, V, a, ?_⟩
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hx)
  let P := (TopCat.Sheaf.pullback (Type v) f).obj F
  refine ⟨i, hWV i hxi, ?_⟩
  have heq := (hcomp i).2
  calc
    P.presheaf.germ U x hx s =
        P.presheaf.germ (W i) x hxi (P.1.map (homOfLE (hWU i)).op s) :=
      (P.presheaf.germ_res_apply (homOfLE (hWU i)) x hxi s).symm
    _ = P.presheaf.germ (W i) x hxi
          (P.1.map (homOfLE (hWV i)).op
            (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
              (op (V i)) (a i))) := congrArg _ heq.symm
    _ = P.presheaf.germ ((Opens.map f).obj (V i)) x (hWV i hxi)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).unit.app F).hom.app
            (op (V i)) (a i)) :=
      P.presheaf.germ_res_apply (homOfLE (hWV i)) x hxi _

end SheafCohomologyExamples.PullbackLocalSections
