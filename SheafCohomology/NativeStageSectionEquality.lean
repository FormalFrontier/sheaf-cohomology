/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier worker-b Hive Task hive-request-83333dedd640d855f159f1c115a70d659ba2c7dc
-/
module
public import SheafCohomology.PullbackLocalSections
public import SpectralStoneDuality.LimitCylinderDescent
public import Mathlib.Geometry.RingedSpace.SheafedSpace

public section

set_option warningAsError true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-!
# Eventual equality of native stage sections

Equality of sections after the actual pullback adjunction unit along a limit
projection is reflected by one transition in a filtered diagram of spectral
sheafed spaces. The result concerns the native stage sheaves and maps.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {J : Type v} [SmallCategory J] [IsFiltered J]
    (N : Jᵒᵖ ⥤ SheafedSpace (Type v))
    (c : Cone (N ⋙ SheafedSpace.forget (Type v))) (hc : IsLimit c)
    (hstage : ∀ k : Jᵒᵖ, SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k))
    (htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
      IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f))

include hc hstage htransition in
/-- If two native sections have equal images under the projection's literal
pullback--pushforward unit, they become equal on the entire inverse image of
their compact open at some later stage. -/
theorem exists_stage_eq_of_pullback_unit_eq (i : J)
    (V : Opens (N.obj (op i))) (hV : IsCompact (V : Set (N.obj (op i))))
    (a b : (N.obj (op i)).presheaf.obj (op V))
    (heq : ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op V) a =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op V) b) :
    ∃ (j : J) (g : i ⟶ j),
      (N.map g.op).hom.c.app (op V) a =
        (N.map g.op).hom.c.app (op V) b := by
  classical
  have hunit : ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
      (N.obj (op i)).sheaf).1.map
        (homOfLE (le_refl ((Opens.map (c.π.app (op i))).obj V))).op
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
          (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op V) a) =
      ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (le_refl ((Opens.map (c.π.app (op i))).obj V))).op
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
            (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app (op V) b) := by
    exact congrArg
      (fun s => ((TopCat.Sheaf.pullback (Type v) (c.π.app (op i))).obj
        (N.obj (op i)).sheaf).1.map
          (homOfLE (le_refl ((Opens.map (c.π.app (op i))).obj V))).op s) heq
  obtain ⟨E₀, hEV, hlimit, hsections⟩ :=
    TopCat.Sheaf.PullbackLocalSections.exists_target_eq_neighborhood
      (c.π.app (op i)) (N.obj (op i)).sheaf V
      ((Opens.map (c.π.app (op i))).obj V) le_rfl a b hunit
  let E : Opens (N.obj (op i)) := E₀
  obtain ⟨X, hX⟩ :=
    (SpectralStoneDuality.limitCylinder_subset_iff_eventually
      (N ⋙ SheafedSpace.forget (Type v)) (op i) hstage htransition c hc
      (V : Set (N.obj (op i))) (E : Set (N.obj (op i)))
      V.isOpen hV E.isOpen).mp (show
        c.π.app (op i) ⁻¹' (V : Set (N.obj (op i))) ⊆
          c.π.app (op i) ⁻¹' (E : Set (N.obj (op i))) from hlimit)
  let j : J := unop X.left
  let g : i ⟶ j := X.hom.unop
  have hStage : (Opens.map (N.map g.op).hom.base).obj E =
      (Opens.map (N.map g.op).hom.base).obj V := by
    apply le_antisymm
    · intro x hx
      exact hEV hx
    · intro x hx
      exact hX hx
  have hmapEV : (Opens.map (N.map g.op).hom.base).obj E ≤
      (Opens.map (N.map g.op).hom.base).obj V := le_of_eq hStage
  have hnat (s : (N.obj (op i)).presheaf.obj (op V)) :
      (N.obj (op j)).presheaf.map (homOfLE hmapEV).op
        ((N.map g.op).hom.c.app (op V) s) =
      (N.map g.op).hom.c.app (op E)
        ((N.obj (op i)).presheaf.map (homOfLE hEV).op s) := by
    have hn := (N.map g.op).hom.c.naturality (homOfLE hEV).op
    change (N.obj (op i)).presheaf.map (homOfLE hEV).op ≫
        (N.map g.op).hom.c.app (op E) =
      (N.map g.op).hom.c.app (op V) ≫
        (N.obj (op j)).presheaf.map (homOfLE hmapEV).op at hn
    simpa [TopCat.Presheaf.pushforward, ConcreteCategory.comp_apply] using
      (ConcreteCategory.congr_hom hn s).symm
  have heqMap : (N.obj (op j)).presheaf.map (homOfLE hmapEV).op
      ((N.map g.op).hom.c.app (op V) a) =
    (N.obj (op j)).presheaf.map (homOfLE hmapEV).op
      ((N.map g.op).hom.c.app (op V) b) := by
    rw [hnat a, hnat b]
    exact congrArg ((N.map g.op).hom.c.app (op E)) (by simpa only [SheafedSpace.sheaf]
      using hsections)
  haveI : IsIso (homOfLE hmapEV).op := by
    letI : IsIso (homOfLE hmapEV) := homOfLE_isIso_of_eq hmapEV hStage
    infer_instance
  haveI : IsIso ((N.obj (op j)).presheaf.map (homOfLE hmapEV).op) := inferInstance
  exact ⟨j, g, (asIso ((N.obj (op j)).presheaf.map
    (homOfLE hmapEV).op)).toEquiv.injective heqMap⟩

include hc hstage htransition in
/-- Equality under the literal projection unit for global sections becomes
equality under a transition of the existing global-section functor. -/
theorem exists_Γ_eq_of_pullback_unit_eq (i : J)
    (a b : (N.rightOp ⋙ SheafedSpace.Γ).obj i)
    (heq : ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
          (op (⊤ : Opens (N.obj (op i)))) a =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v)
        (c.π.app (op i))).unit.app (N.obj (op i)).sheaf).hom.app
          (op (⊤ : Opens (N.obj (op i)))) b) :
    ∃ (j : J) (g : i ⟶ j),
      (N.rightOp ⋙ SheafedSpace.Γ).map g a =
        (N.rightOp ⋙ SheafedSpace.Γ).map g b := by
  letI : SpectralSpace (N.obj (op i)) := hstage (op i)
  have hcompact : IsCompact ((⊤ : Opens (N.obj (op i))) : Set (N.obj (op i))) :=
    isCompact_univ
  obtain ⟨j, g, hab⟩ := exists_stage_eq_of_pullback_unit_eq
    N c hc hstage htransition i ⊤ hcompact a b heq
  refine ⟨j, g, ?_⟩
  simpa [TopCat.Presheaf.pushforward, Functor.comp_obj, Functor.comp_map,
    Functor.rightOp_map, SheafedSpace.Γ_map_op] using hab

end AlgebraicGeometry.SheafedSpace
