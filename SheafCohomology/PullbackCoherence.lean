/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.Topology.Sheaves.Functors

public section

set_option warningAsError true

/-!
# Coherence for pullback of sheaves

This file packages the canonical identity and composition comparisons for
pullback of sheaves.  The comparisons are obtained from uniqueness of left
adjoints to the definitionally compatible pushforward functors.

The topological-space universe is also the universe of coefficient carriers
and morphisms, as required by mathlib's current sheaf-pullback API.  The
coefficient category's object universe remains independent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace TopCat.Sheaf

variable (A : Type u) [Category.{w} A]
variable {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
variable [ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
variable [PreservesLimits (CategoryTheory.forget A)]
variable [PreservesFilteredColimits (CategoryTheory.forget A)]
variable [(CategoryTheory.forget A).ReflectsIsomorphisms]

variable {X Y Z : TopCat.{w}}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Pushforward along the identity, used to normalize the left-adjoint
identity comparison. -/
private noncomputable def pushforwardIdIso (X : TopCat.{w}) :
    pushforward A (𝟙 X) ≅ 𝟭 (X.Sheaf A) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Composition of pushforwards, used to normalize the corresponding
left-adjoint comparison. -/
private noncomputable def pushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforward A f ⋙ pushforward A g ≅ pushforward A (f ≫ g) :=
  Iso.refl _

/-- Pullback along a composite is canonically isomorphic to iterated pullback. -/
@[expose] noncomputable def pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback A g ⋙ pullback A f ≅ pullback A (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction A g)
    (pullbackPushforwardAdjunction A f)
    (pullbackPushforwardAdjunction A (f ≫ g))
    (Iso.refl _)

private theorem pullbackCompIso_eq_privateConstruction
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackCompIso A f g =
      Adjunction.leftAdjointCompIso
        (pullbackPushforwardAdjunction A g)
        (pullbackPushforwardAdjunction A f)
        (pullbackPushforwardAdjunction A (f ≫ g))
        (pushforwardCompIso A f g) :=
  rfl

/-- The forward composite-pullback comparison on one sheaf. -/
noncomputable abbrev pullbackCompHom (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Sheaf A) :
    (pullback A f).obj ((pullback A g).obj F) ⟶
      (pullback A (f ≫ g)).obj F :=
  (pullbackCompIso A f g).hom.app F

/-- The inverse composite-pullback comparison on one sheaf. -/
noncomputable abbrev pullbackCompInv (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : Z.Sheaf A) :
    (pullback A (f ≫ g)).obj F ⟶
      (pullback A f).obj ((pullback A g).obj F) :=
  (pullbackCompIso A f g).inv.app F

/-- The forward composite-pullback comparison is natural in the sheaf. -/
theorem pullbackCompHom_naturality (f : X ⟶ Y) (g : Y ⟶ Z)
    {F G : Z.Sheaf A} (α : F ⟶ G) :
    (pullback A f).map ((pullback A g).map α) ≫
        pullbackCompHom A f g G =
      pullbackCompHom A f g F ≫ (pullback A (f ≫ g)).map α :=
  (pullbackCompIso A f g).hom.naturality α

/-- The inverse composite-pullback comparison is natural in the sheaf. -/
theorem pullbackCompInv_naturality (f : X ⟶ Y) (g : Y ⟶ Z)
    {F G : Z.Sheaf A} (α : F ⟶ G) :
    (pullback A (f ≫ g)).map α ≫ pullbackCompInv A f g G =
      pullbackCompInv A f g F ≫
        (pullback A f).map ((pullback A g).map α) :=
  (pullbackCompIso A f g).inv.naturality α

/-- Pullback along the identity is canonically isomorphic to the identity functor. -/
@[expose] noncomputable def pullbackIdIso (X : TopCat.{w}) :
    pullback A (𝟙 X) ≅ 𝟭 (X.Sheaf A) :=
  Adjunction.leftAdjointIdIso
    (pullbackPushforwardAdjunction A (𝟙 X)) (Iso.refl _)

private theorem pullbackIdIso_eq_privateConstruction (X : TopCat.{w}) :
    pullbackIdIso A X =
      Adjunction.leftAdjointIdIso
        (pullbackPushforwardAdjunction A (𝟙 X)) (pushforwardIdIso A X) :=
  rfl

/-- The identity-pullback comparison on one sheaf. -/
noncomputable abbrev pullbackIdHom (X : TopCat.{w}) (F : X.Sheaf A) :
    (pullback A (𝟙 X)).obj F ⟶ F :=
  (pullbackIdIso A X).hom.app F

/-- The inverse identity-pullback comparison on one sheaf. -/
noncomputable abbrev pullbackIdInv (X : TopCat.{w}) (F : X.Sheaf A) :
    F ⟶ (pullback A (𝟙 X)).obj F :=
  (pullbackIdIso A X).inv.app F

/-- The forward identity-pullback comparison is natural in the sheaf. -/
theorem pullbackIdHom_naturality (X : TopCat.{w}) {F G : X.Sheaf A}
    (α : F ⟶ G) :
    (pullback A (𝟙 X)).map α ≫ pullbackIdHom A X G =
      pullbackIdHom A X F ≫ α :=
  (pullbackIdIso A X).hom.naturality α

/-- The inverse identity-pullback comparison is natural in the sheaf. -/
theorem pullbackIdInv_naturality (X : TopCat.{w}) {F G : X.Sheaf A}
    (α : F ⟶ G) :
    α ≫ pullbackIdInv A X G =
      pullbackIdInv A X F ≫ (pullback A (𝟙 X)).map α :=
  (pullbackIdIso A X).inv.naturality α

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [HasColimits A] [HasLimits A] in
private theorem pushforwardCompIso_comp_id (f : X ⟶ Y) :
    pushforwardCompIso A f (𝟙 Y) =
      Functor.isoWhiskerLeft (pushforward A f) (pushforwardIdIso A Y) ≪≫
        (pushforward A f).rightUnitor := by
  ext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  simp [pushforwardCompIso, pushforwardIdIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [HasColimits A] [HasLimits A] in
private theorem pushforwardCompIso_id_comp (f : X ⟶ Y) :
    pushforwardCompIso A (𝟙 X) f =
      Functor.isoWhiskerRight (pushforwardIdIso A X) (pushforward A f) ≪≫
        (pushforward A f).leftUnitor := by
  ext F
  apply CategoryTheory.Sheaf.hom_ext
  ext U
  simp [pushforwardCompIso, pushforwardIdIso]
  change 𝟙 _ = 𝟙 _
  rfl

/-- Pullback composition agrees with the identity comparison when the first
map is an identity. -/
theorem pullbackCompIso_comp_id (f : X ⟶ Y) :
    pullbackCompIso A (𝟙 X) f =
      Functor.isoWhiskerLeft (pullback A f) (pullbackIdIso A X) ≪≫
        (pullback A f).rightUnitor :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _
    (pushforwardCompIso_id_comp A f)

/-- Pullback composition agrees with the identity comparison when the second
map is an identity. -/
theorem pullbackCompIso_id_comp (f : X ⟶ Y) :
    pullbackCompIso A f (𝟙 Y) =
      Functor.isoWhiskerRight (pullbackIdIso A Y) (pullback A f) ≪≫
        (pullback A f).leftUnitor :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _
    (pushforwardCompIso_comp_id A f)

omit [HasColimits A] [HasLimits A] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem pushforwardCompIso_assoc
    {W : TopCat.{w}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft (pushforward A f) (pushforwardCompIso A g h) ≪≫
        pushforwardCompIso A f (g ≫ h) =
      (Functor.associator (pushforward A f) (pushforward A g)
          (pushforward A h)).symm ≪≫
        Functor.isoWhiskerRight (pushforwardCompIso A f g)
          (pushforward A h) ≪≫
        pushforwardCompIso A (f ≫ g) h := by
  ext F
  simp [pushforwardCompIso]
  erw [Category.comp_id]

/-- The two canonical comparisons from a triple iterated pullback to pullback
along the triple composite agree. -/
theorem pullbackCompIso_assoc
    {W : TopCat.{w}} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    Functor.isoWhiskerLeft (pullback A h) (pullbackCompIso A f g) ≪≫
        pullbackCompIso A (f ≫ g) h =
      (Functor.associator (pullback A h) (pullback A g)
          (pullback A f)).symm ≪≫
        Functor.isoWhiskerRight (pullbackCompIso A g h)
          (pullback A f) ≪≫
        pullbackCompIso A f (g ≫ h) :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (pushforwardCompIso_assoc A f g h)

#print axioms pullbackCompIso_eq_privateConstruction
#print axioms pullbackIdIso_eq_privateConstruction

end TopCat.Sheaf
