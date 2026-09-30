/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.AbelianForget.Pullback
public import Mathlib.Geometry.RingedSpace.SheafedSpace

public section

set_option warningAsError true

/-!
# Forgetting additive structure on sheafed spaces

The native presheaf coefficient functor preserves the carrier and structure
maps. The existing sheaf-composition functor supplies its sheaf condition.
-/

universe v

open CategoryTheory CategoryTheory.Functor TopologicalSpace TopCat.Sheaf.AbelianForget

namespace AlgebraicGeometry.SheafedSpace.AbelianForget

/-- Forget the additive structure of a sheafed space, without changing its
underlying topological space or its presheaf morphisms. -/
@[expose] noncomputable def underlying :
    SheafedSpace AddCommGrpCat.{v} ⥤ SheafedSpace (Type v) where
  obj X :=
    { toPresheafedSpace :=
        (CategoryTheory.forget AddCommGrpCat.{v}).mapPresheaf.obj X.toPresheafedSpace
      IsSheaf := ((underlyingSheaf (X : TopCat)).obj X.sheaf).property }
  map f := InducedCategory.homMk
    ((CategoryTheory.forget AddCommGrpCat.{v}).mapPresheaf.map f.hom)
  map_id X := by
    apply InducedCategory.hom_ext
    exact (CategoryTheory.forget AddCommGrpCat.{v}).mapPresheaf.map_id X.toPresheafedSpace
  map_comp f g := by
    apply InducedCategory.hom_ext
    exact (CategoryTheory.forget AddCommGrpCat.{v}).mapPresheaf.map_comp f.hom g.hom

@[simp] theorem underlying_obj_carrier (X : SheafedSpace AddCommGrpCat.{v}) :
    ((underlying.obj X : SheafedSpace (Type v)) : TopCat) = (X : TopCat) := rfl

@[simp] theorem underlying_obj_presheaf (X : SheafedSpace AddCommGrpCat.{v}) :
    (underlying.obj X).presheaf = X.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v} := rfl

@[simp] theorem underlying_obj_sheaf (X : SheafedSpace AddCommGrpCat.{v}) :
    (underlying.obj X).sheaf = (underlyingSheaf (X : TopCat)).obj X.sheaf := rfl

@[simp] theorem underlying_map_base {X Y : SheafedSpace AddCommGrpCat.{v}} (f : X ⟶ Y) :
    (underlying.map f).hom.base = f.hom.base := rfl

@[simp] theorem underlying_map_c {X Y : SheafedSpace AddCommGrpCat.{v}} (f : X ⟶ Y) :
    (underlying.map f).hom.c =
      whiskerRight f.hom.c (CategoryTheory.forget AddCommGrpCat.{v}) := rfl

/-- Forgetting to the actual presheafed-space coefficient functor commutes strictly. -/
theorem underlying_forgetToPresheafedSpace :
    underlying ⋙ (SheafedSpace.forgetToPresheafedSpace (C := Type v)) =
      (SheafedSpace.forgetToPresheafedSpace (C := AddCommGrpCat.{v})) ⋙
        (CategoryTheory.forget AddCommGrpCat.{v}).mapPresheaf := by
  rfl

/-- Forgetting to the actual topological-space functor commutes strictly. -/
theorem underlying_forget :
    underlying ⋙ SheafedSpace.forget (Type v) =
      SheafedSpace.forget AddCommGrpCat.{v} := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The mate of an actual sheafed-space arrow is the canonical comparison
followed by the forgotten additive mate, with no assumption on the arrow. -/
theorem underlying_map_pullback_mate {X Y : SheafedSpace AddCommGrpCat.{v}} (f : X ⟶ Y) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f.hom.base).homEquiv
      ((underlyingSheaf (Y : TopCat)).obj Y.sheaf)
      ((underlyingSheaf (X : TopCat)).obj X.sheaf)).symm
        (⟨(underlying.map f).hom.c⟩) =
      canonicalComponent f.hom.base Y.sheaf ≫
        (underlyingSheaf (X : TopCat)).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f.hom.base).homEquiv
            Y.sheaf X.sheaf).symm (⟨f.hom.c⟩)) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f.hom.base).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  rw [canonicalComponent_mate_map]
  rw [Equiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.SheafedSpace.AbelianForget
