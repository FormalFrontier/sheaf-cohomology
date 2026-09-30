/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/


module
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import SheafCohomology.OpenBaseChange

public section

set_option warningAsError true
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Native restriction to an inverse-image open

A morphism of sheafed spaces restricts canonically to the inverse image of an
open subset of its target.  The morphism is the existing open-immersion lift,
not an independently constructed morphism of sheaves.
-/

open CategoryTheory TopologicalSpace Opposite

universe v

noncomputable section

namespace AlgebraicGeometry.SheafedSpace

variable {C : Type (v + 1)} [Category.{v} C]
variable {X Y Z : SheafedSpace.{v + 1, v, v} C}

/-- The inclusion of the inverse-image open contains the composite's image. -/
theorem restrictOnPreimage_range (g : X ⟶ Y) (V : Opens Y) :
    Set.range (X.ofRestrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ≫ g).hom.base ⊆
      Set.range (Y.ofRestrict V.isOpenEmbedding).hom.base := by
  rintro _ ⟨point, rfl⟩
  exact ⟨⟨g.hom.base point.1, point.2⟩, rfl⟩

/-- The native sheafed-space arrow over the inverse-image open of `V`.
Its defining property is the commuting square with the restriction inclusions. -/
@[expose] def restrictOnPreimage (g : X ⟶ Y) (V : Opens Y) :
    X.restrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ⟶
      Y.restrict V.isOpenEmbedding := by
  let inclusion := (Y.ofRestrict V.isOpenEmbedding).hom
  let composite := (X.ofRestrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ≫ g).hom
  haveI : PresheafedSpace.IsOpenImmersion inclusion := by
    dsimp [inclusion]
    infer_instance
  exact InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
    inclusion composite (restrictOnPreimage_range g V))

/-- The canonical restriction arrow commutes with both native inclusions. -/
theorem restrictOnPreimage_fac (g : X ⟶ Y) (V : Opens Y) :
    restrictOnPreimage g V ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ≫ g := by
  apply InducedCategory.hom_ext
  unfold restrictOnPreimage
  dsimp
  exact PresheafedSpace.IsOpenImmersion.lift_fac _ _ (restrictOnPreimage_range g V)

/-- The native restriction arrow is unique with its inclusion square. -/
theorem restrictOnPreimage_unique (g : X ⟶ Y) (V : Opens Y)
    (arrow : X.restrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ⟶
      Y.restrict V.isOpenEmbedding)
    (comm : arrow ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict ((Opens.map g.hom.base).obj V).isOpenEmbedding ≫ g) :
    arrow = restrictOnPreimage g V := by
  apply InducedCategory.hom_ext
  unfold restrictOnPreimage
  dsimp
  apply PresheafedSpace.IsOpenImmersion.lift_uniq _ _ (restrictOnPreimage_range g V)
  exact congrArg (fun morphism => morphism.hom) comm

/-- The continuous map of the native arrow is the official open-base-change map. -/
theorem restrictOnPreimage_base (g : X ⟶ Y) (V : Opens Y) :
    (restrictOnPreimage g V).hom.base =
      TopCat.Sheaf.OpenBaseChange.preimageMap g.hom.base V := by
  haveI : Mono V.inclusion' := (TopCat.mono_iff_injective _).mpr V.isOpenEmbedding.injective
  apply (cancel_mono V.inclusion').1
  exact (congrArg (fun arrow => arrow.hom.base) (restrictOnPreimage_fac g V)).trans
    (TopCat.Sheaf.OpenBaseChange.preimageMap_comp_inclusion g.hom.base V).symm

/-- Transport the source restriction along an explicitly named inverse-image open. -/
@[expose] def restrictOnNamedPreimage (g : X ⟶ Y) (V : Opens Y)
    (U : Opens X) (h : U = (Opens.map g.hom.base).obj V) :
    X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding :=
  eqToHom (congrArg (fun W : Opens X => X.restrict W.isOpenEmbedding) h) ≫
    restrictOnPreimage g V

/-- The named-open restriction still commutes with the canonical inclusions. -/
theorem restrictOnNamedPreimage_fac (g : X ⟶ Y) (V : Opens Y)
    (U : Opens X) (h : U = (Opens.map g.hom.base).obj V) :
    restrictOnNamedPreimage g V U h ≫ Y.ofRestrict V.isOpenEmbedding =
      X.ofRestrict U.isOpenEmbedding ≫ g := by
  subst U
  simpa [restrictOnNamedPreimage] using restrictOnPreimage_fac g V

/-- Restricting an identity gives the identity, after the inverse-image equality cast. -/
theorem restrictOnNamedPreimage_id
    (X : SheafedSpace.{v + 1, v, v} C) (V : Opens X) :
    restrictOnNamedPreimage (𝟙 X) V V (Opens.map_id_obj V).symm =
      𝟙 (X.restrict V.isOpenEmbedding) := by
  apply (cancel_mono (X.ofRestrict V.isOpenEmbedding)).1
  simpa only [Category.id_comp, Category.comp_id] using
    restrictOnNamedPreimage_fac (𝟙 X) V V (Opens.map_id_obj V).symm

/-- Two restriction arrows compose, with the inverse-image equality transport. -/
theorem restrictOnPreimage_comp (f : X ⟶ Y) (g : Y ⟶ Z) (W : Opens Z) :
    restrictOnNamedPreimage f ((Opens.map g.hom.base).obj W)
        ((Opens.map (f ≫ g).hom.base).obj W)
        (Opens.map_comp_obj f.hom.base g.hom.base W) ≫
      restrictOnPreimage g W = restrictOnPreimage (f ≫ g) W := by
  apply (cancel_mono (Z.ofRestrict W.isOpenEmbedding)).1
  calc
    (restrictOnNamedPreimage f ((Opens.map g.hom.base).obj W)
          ((Opens.map (f ≫ g).hom.base).obj W)
          (Opens.map_comp_obj f.hom.base g.hom.base W) ≫
        restrictOnPreimage g W) ≫ Z.ofRestrict W.isOpenEmbedding =
        restrictOnNamedPreimage f ((Opens.map g.hom.base).obj W)
          ((Opens.map (f ≫ g).hom.base).obj W)
          (Opens.map_comp_obj f.hom.base g.hom.base W) ≫
          (Y.ofRestrict ((Opens.map g.hom.base).obj W).isOpenEmbedding ≫ g) := by
            rw [Category.assoc, restrictOnPreimage_fac]
    _ = X.ofRestrict ((Opens.map (f ≫ g).hom.base).obj W).isOpenEmbedding ≫
          (f ≫ g) := by
            rw [← Category.assoc, restrictOnNamedPreimage_fac, Category.assoc]
    _ = restrictOnPreimage (f ≫ g) W ≫ Z.ofRestrict W.isOpenEmbedding :=
      (restrictOnPreimage_fac (f ≫ g) W).symm

/-- Global sections of the restriction are sections on the chosen open. -/
theorem restrict_Γ_obj (X : SheafedSpace.{v + 1, v, v} C) (U : Opens X) :
    Γ.obj (op (X.restrict U.isOpenEmbedding)) = X.presheaf.obj (op U) := by
  change X.presheaf.obj (op (U.isOpenEmbedding.functor.obj ⊤)) = _
  rw [Opens.isOpenEmbedding_obj_top]

/-- The inclusion's component on its defining open is the canonical transport
from sections on that open to sections of the restriction. -/
theorem ofRestrict_c_app_self
    (X : SheafedSpace.{v + 1, v, v} C) (U : Opens X) :
    (X.ofRestrict U.isOpenEmbedding).hom.c.app (op U) =
      eqToHom (restrict_Γ_obj X U).symm ≫
        (X.restrict U.isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op (show
            (Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base).obj U = ⊤ by
              change (Opens.map U.inclusion').obj U = ⊤
              exact Opens.inclusion'_map_eq_top U).symm)) := by
  rw [ofRestrict_hom_c_app, Opens.adjunction_counit_app_self U]
  simp only [eqToHom_op, eqToHom_map]
  exact (eqToHom_trans _ _).symm

/-- On global sections, the restricted native arrow is the original
presheaf morphism's component on the target open, with equality transports. -/
theorem restrictOnPreimage_Γ_map (g : X ⟶ Y) (V : Opens Y) :
    eqToHom (restrict_Γ_obj Y V).symm ≫
        Γ.map (restrictOnPreimage g V).op ≫
        eqToHom (restrict_Γ_obj X ((Opens.map g.hom.base).obj V)) =
      g.hom.c.app (op V) := by
  have square := congr_hom_app (restrictOnPreimage_fac g V) (op V)
  simp only [comp_hom_c_app'] at square
  rw [ofRestrict_c_app_self Y V,
    ofRestrict_c_app_self X ((Opens.map g.hom.base).obj V)] at square
  have hV : (Opens.map (Y.ofRestrict V.isOpenEmbedding).hom.base).obj V = ⊤ := by
    change (Opens.map V.inclusion').obj V = ⊤
    exact Opens.inclusion'_map_eq_top V
  have naturality := (restrictOnPreimage g V).hom.c.naturality
    (eqToHom (congrArg op hV.symm))
  simp only [eqToHom_map] at square naturality
  rw [Category.assoc, naturality] at square
  simp only [Category.assoc, eqToHom_trans] at square
  let tail :=
    ((TopCat.Presheaf.pushforward C (restrictOnPreimage g V).hom.base).obj
      (X.restrict ((Opens.map g.hom.base).obj V).isOpenEmbedding).presheaf).map
      (eqToHom (congrArg op hV.symm))
  haveI : Mono tail := by
    dsimp [tail]
    infer_instance
  have key :
      eqToHom (restrict_Γ_obj Y V).symm ≫ Γ.map (restrictOnPreimage g V).op =
        g.hom.c.app (op V) ≫
          eqToHom (restrict_Γ_obj X ((Opens.map g.hom.base).obj V)).symm := by
    apply (cancel_mono tail).1
    simpa only [Γ_map_op, tail, Category.assoc, eqToHom_map, eqToHom_trans] using square
  rw [← Category.assoc, key]
  simp

/-- The section component of a named-open arrow includes the explicit
transport from the canonical inverse image to the chosen name. -/
theorem restrictOnNamedPreimage_Γ_map (g : X ⟶ Y) (V : Opens Y)
    (U : Opens X) (h : U = (Opens.map g.hom.base).obj V) :
    eqToHom (restrict_Γ_obj Y V).symm ≫
        Γ.map (restrictOnNamedPreimage g V U h).op ≫
        eqToHom (restrict_Γ_obj X U) =
      g.hom.c.app (op V) ≫
        eqToHom (congrArg (fun W : Opens X => X.presheaf.obj (op W)) h.symm) := by
  cases h
  simpa [restrictOnNamedPreimage] using restrictOnPreimage_Γ_map g V

end AlgebraicGeometry.SheafedSpace
