/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Adapted from SheafCohomology.AbelianForget.Pullback by Anchor (source maintainer).
-/


module
public import SheafCohomology.CommRingForget.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import SheafCohomology.PullbackCoherence

public section

/-!
# Forgetting commutative-ring sheaves and pullback

The comparison is the native Type-valued pullback/pushforward mate of the
forgotten ring unit. It is an isomorphism for every continuous map.

Ring adaptation: Formal Frontier Agents. The original additive proof
is credited to Anchor. This ring-specialized
mate proof adapts the expression and proof outline of published
`SheafCohomology.AbelianForget.Pullback` at
`e4c7d681e0913fc1dde266cfcfc37763f1d47785`
(Anchor, source maintainer); it uses mathlib Kan extension and sheafification APIs.
-/

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.CommRingForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)
/-- The comparison from pullback of the underlying sheaf to the underlying
ring pullback, defined as the native Type-valued adjunction mate of the
forgotten ring unit. -/
noncomputable def canonicalComponent (A : Y.Sheaf CommRingCat.{v}) :
    (TopCat.Sheaf.pullback (Type v) g).obj ((underlyingSheaf Y).obj A) ⟶
      (underlyingSheaf X).obj ((TopCat.Sheaf.pullback CommRingCat.{v} g).obj A) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _).symm
    ((underlyingSheaf Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A))

/-- The canonical comparison is the mate of the forgotten ring unit. -/
theorem canonicalComponent_mate (A : Y.Sheaf CommRingCat.{v}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _
      (canonicalComponent g A) =
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A) := by
  exact Equiv.apply_symm_apply _ _

/-- The mate law for an arbitrary morphism out of the ring pullback. -/
theorem canonicalComponent_mate_map (A : Y.Sheaf CommRingCat.{v})
    (B : X.Sheaf CommRingCat.{v})
    (a : (TopCat.Sheaf.pullback CommRingCat.{v} g).obj A ⟶ B) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _
      (canonicalComponent g A ≫ (underlyingSheaf X).map a) =
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).homEquiv A B a) := by
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv_naturality_right,
    canonicalComponent_mate]
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).homEquiv_unit]
  change (underlyingSheaf Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A) ≫
      (underlyingSheaf Y).map ((TopCat.Sheaf.pushforward CommRingCat.{v} g).map a) =
    (underlyingSheaf Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A ≫
        (TopCat.Sheaf.pushforward CommRingCat.{v} g).map a)
  exact ((underlyingSheaf Y).map_comp _ _).symm

/-- Naturality of the pullback/forgetful comparison. -/
theorem canonicalComponent_naturality {A B : Y.Sheaf CommRingCat.{v}}
    (a : A ⟶ B) :
    (TopCat.Sheaf.pullback (Type v) g).map ((underlyingSheaf Y).map a) ≫
      canonicalComponent g B =
      canonicalComponent g A ≫
        (underlyingSheaf X).map ((TopCat.Sheaf.pullback CommRingCat.{v} g).map a) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _).injective
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv_naturality_left,
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv_naturality_right,
    canonicalComponent_mate, canonicalComponent_mate]
  change (underlyingSheaf Y).map a ≫
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app B) =
    (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A) ≫
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pushforward CommRingCat.{v} g).map
          ((TopCat.Sheaf.pullback CommRingCat.{v} g).map a))
  rw [← (underlyingSheaf Y).map_comp, ← (underlyingSheaf Y).map_comp]
  exact congrArg (underlyingSheaf Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.naturality a)

/-- The natural transformation whose components are native adjunction mates. -/
@[expose] noncomputable def canonicalComparison :
    underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g ⟶
      TopCat.Sheaf.pullback CommRingCat.{v} g ⋙ underlyingSheaf X where
  app := canonicalComponent g
  naturality := by
    intro A B a
    exact canonicalComponent_naturality g a

/-- The component of the natural transformation is the native mate. -/
@[simp] theorem canonicalComparison_app (A : Y.Sheaf CommRingCat.{v}) :
    (canonicalComparison g).app A = canonicalComponent g A := rfl

private noncomputable def presheafPullbackForgetIso :
    TopCat.Presheaf.pullback CommRingCat.{v} g ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{v}) ≅
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{v}) ⋙
      TopCat.Presheaf.pullback (Type v) g := by
  let : CategoryTheory.RepresentablyFlat (Opens.map g) :=
    CategoryTheory.flat_of_preservesFiniteLimits (Opens.map g)
  exact Functor.lanCompIsoOfPreserves (CategoryTheory.forget CommRingCat.{v}) (Opens.map g).op

private theorem presheafPullbackForget_unit (P : Y.Presheaf CommRingCat.{v}) :
    ((Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{v})).map
        ((Opens.map g).op.lanUnit.app P) =
      (Opens.map g).op.lanUnit.app (P ⋙ (CategoryTheory.forget CommRingCat.{v})) ≫
        ((Functor.whiskeringLeft _ _ _).obj (Opens.map g).op).map
          ((presheafPullbackForgetIso g).app P).inv := by
  exact (Functor.leftKanExtensionCompIsoOfPreserves_inv_fac
    (CategoryTheory.forget CommRingCat.{v}) P (Opens.map g).op).symm

private noncomputable def localSheafifyForgetIso (P : X.Presheaf CommRingCat.{v}) :
    (presheafToSheaf (Opens.grothendieckTopology X) (Type v)).obj
        (P ⋙ (CategoryTheory.forget CommRingCat.{v})) ≅
      (underlyingSheaf X).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{v}).obj P) :=
  (sheafComposeNatIso (Opens.grothendieckTopology X)
      (CategoryTheory.forget CommRingCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v))).app P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem sheafification_unit_bridge (Q : X.Presheaf CommRingCat.{v})
    (R : X.Presheaf (Type v)) (ρ : Q ⋙ CategoryTheory.forget CommRingCat.{v} ≅ R) :
    (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)).unit.app R ≫
        (TopCat.Sheaf.forget (Type v) X).map
          ((presheafToSheaf (Opens.grothendieckTopology X) (Type v)).mapIso ρ).inv ≫
        (TopCat.Sheaf.forget (Type v) X).map (localSheafifyForgetIso Q).hom =
      ρ.inv ≫ whiskerRight
        ((sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v}).unit.app Q)
          (CategoryTheory.forget CommRingCat.{v}) := by
  have hUnit := (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)).unit.naturality ρ.inv
  have hCompose := sheafComposeNatTrans_fac (Opens.grothendieckTopology X)
    (CategoryTheory.forget CommRingCat.{v})
    (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v})
    (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)) Q
  calc
    _ = ρ.inv ≫
        (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)).unit.app
          (Q ⋙ CategoryTheory.forget CommRingCat.{v}) ≫
        (TopCat.Sheaf.forget (Type v) X).map (localSheafifyForgetIso Q).hom := by
          rw [← Category.assoc]
          exact congrArg (fun arrow => arrow ≫ (TopCat.Sheaf.forget (Type v) X).map
            (localSheafifyForgetIso Q).hom) hUnit.symm
    _ = _ := by
      exact congrArg (fun arrow => ρ.inv ≫ arrow) hCompose

private noncomputable def constructionComparisonIso (A : Y.Sheaf CommRingCat.{v}) :
    (Functor.sheafPullbackConstruction.sheafPullback (Opens.map g) (Type v)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
        ((underlyingSheaf Y).obj A) ≅
      (underlyingSheaf X).obj
        ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map g) CommRingCat.{v}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj A) :=
  ((presheafToSheaf (Opens.grothendieckTopology X) (Type v)).mapIso
    ((presheafPullbackForgetIso g).app ((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A))).symm ≪≫
      localSheafifyForgetIso
        ((TopCat.Presheaf.pullback CommRingCat.{v} g).obj
          ((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A))

private noncomputable def constructedInverse (A : Y.Sheaf CommRingCat.{v}) :
    (underlyingSheaf X).obj ((TopCat.Sheaf.pullback CommRingCat.{v} g).obj A) ≅
      (TopCat.Sheaf.pullback (Type v) g).obj ((underlyingSheaf Y).obj A) :=
  (underlyingSheaf X).mapIso ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).app A) ≪≫
    (localSheafifyForgetIso
      ((TopCat.Presheaf.pullback CommRingCat.{v} g).obj
        ((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A))).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) (Type v)).mapIso
      ((presheafPullbackForgetIso g).app
        ((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A)) ≪≫
    ((TopCat.Sheaf.pullbackIso (Type v) g).app ((underlyingSheaf Y).obj A)).symm

private theorem constructedRingUnit_forget (A : Y.Sheaf CommRingCat.{v}) :
    (TopCat.Sheaf.forget CommRingCat.{v} Y).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          CommRingCat.{v} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app A) =
      (((Opens.map g).op.lanAdjunction CommRingCat.{v}).comp
        (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v})).unit.app
          ((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A) := by
  let adj := ((Opens.map g).op.lanAdjunction CommRingCat.{v}).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v})
  let commRight :
      𝟭 (X.Sheaf CommRingCat.{v}) ⋙
          sheafToPresheaf (Opens.grothendieckTopology X) CommRingCat.{v} ⋙
            (Functor.whiskeringLeft _ _ _).obj (Opens.map g).op ≅
        TopCat.Sheaf.pushforward CommRingCat.{v} g ⋙
          sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{v} := Iso.refl _
  let commLeft :
      sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{v} ⋙
          (Opens.map g).op.lan ⋙
            presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{v} ≅
        Functor.sheafPullbackConstruction.sheafPullback (Opens.map g) CommRingCat.{v}
            (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) ⋙
          𝟭 (X.Sheaf CommRingCat.{v}) := Iso.refl _
  have unit_eq := adj.map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{v})
    (Functor.FullyFaithful.id _) commLeft commRight A
  simp [adj, commLeft, commRight, Adjunction.comp_unit_app] at unit_eq
  exact unit_eq

private theorem constructedTypeUnit_forget (A : Y.Sheaf (Type v)) :
    (TopCat.Sheaf.forget (Type v) Y).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          (Type v) (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app A) =
      (((Opens.map g).op.lanAdjunction (Type v)).comp
        (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v))).unit.app
          ((TopCat.Sheaf.forget (Type v) Y).obj A) := by
  let adj := ((Opens.map g).op.lanAdjunction (Type v)).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v))
  let commRight :
      𝟭 (X.Sheaf (Type v)) ⋙
          sheafToPresheaf (Opens.grothendieckTopology X) (Type v) ⋙
            (Functor.whiskeringLeft _ _ _).obj (Opens.map g).op ≅
        TopCat.Sheaf.pushforward (Type v) g ⋙
          sheafToPresheaf (Opens.grothendieckTopology Y) (Type v) := Iso.refl _
  let commLeft :
      sheafToPresheaf (Opens.grothendieckTopology Y) (Type v) ⋙
          (Opens.map g).op.lan ⋙
            presheafToSheaf (Opens.grothendieckTopology X) (Type v) ≅
        Functor.sheafPullbackConstruction.sheafPullback (Opens.map g) (Type v)
            (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) ⋙
          𝟭 (X.Sheaf (Type v)) := Iso.refl _
  have unit_eq := adj.map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) (Type v))
    (Functor.FullyFaithful.id _) commLeft commRight A
  simp [adj, commLeft, commRight, Adjunction.comp_unit_app] at unit_eq
  exact unit_eq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem construction_unit_bridge (A : Y.Sheaf CommRingCat.{v}) :
    (underlyingSheaf Y).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          CommRingCat.{v} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app A) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          (Type v) (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app ((underlyingSheaf Y).obj A) ≫
        (TopCat.Sheaf.pushforward (Type v) g).map ((constructionComparisonIso g A).hom) := by
  apply (TopCat.Sheaf.forget (Type v) Y).map_injective
  change ((Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget CommRingCat.{v})).map
    ((TopCat.Sheaf.forget CommRingCat.{v} Y).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        CommRingCat.{v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app A)) =
    (TopCat.Sheaf.forget (Type v) Y).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        (Type v) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app ((underlyingSheaf Y).obj A)) ≫
      ((Functor.whiskeringLeft _ _ _).obj (Opens.map g).op).map
        ((TopCat.Sheaf.forget (Type v) X).map ((constructionComparisonIso g A).hom))
  rw [constructedRingUnit_forget, constructedTypeUnit_forget]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  rw [Functor.map_comp]
  simp only [constructionComparisonIso, Iso.trans_hom, Iso.symm_hom]
  rw [Functor.map_comp, Functor.map_comp]
  rw [Functor.lanAdjunction_unit, Functor.lanAdjunction_unit]
  rw [presheafPullbackForget_unit]
  change ((Opens.map g).op.lanUnit.app
      (((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A) ⋙ CategoryTheory.forget CommRingCat.{v}) ≫
        whiskerLeft (Opens.map g).op
          ((presheafPullbackForgetIso g).app
            ((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A)).inv) ≫
      whiskerLeft (Opens.map g).op
        (whiskerRight
          ((sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat.{v}).unit.app
            ((Opens.map g).op.lan.obj
              ((TopCat.Sheaf.forget CommRingCat.{v} Y).obj A)))
          (CategoryTheory.forget CommRingCat.{v})) = _
  let P := (TopCat.Sheaf.forget CommRingCat.{v} Y).obj A
  let Q := ((Opens.map g).op.lan).obj P
  let R := ((Opens.map g).op.lan).obj (P ⋙ CategoryTheory.forget CommRingCat.{v})
  let rho := (presheafPullbackForgetIso g).app P
  have hSheaf := sheafification_unit_bridge Q R rho
  convert congrArg (fun arrow =>
    (Opens.map g).op.lanUnit.app (P ⋙ CategoryTheory.forget CommRingCat.{v}) ≫
      whiskerLeft (Opens.map g).op arrow) hSheaf.symm using 1 <;>
    simp only [Category.assoc]
  all_goals rfl

private theorem abstractTypeUnit_toConstruction (A : Y.Sheaf (Type v)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).unit.app A ≫
      (TopCat.Sheaf.pushforward (Type v) g).map
        ((TopCat.Sheaf.pullbackIso (Type v) g).hom.app A) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        (Type v) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app A := by
  exact Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
      (Type v) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem abstractRingUnit_fromConstruction (A : Y.Sheaf CommRingCat.{v}) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        CommRingCat.{v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app A ≫
      (TopCat.Sheaf.pushforward CommRingCat.{v} g).map
        ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A := by
  have unit_eq := Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
      CommRingCat.{v} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) A
  rw [← unit_eq, Category.assoc, ← Functor.map_comp,
    show ((Adjunction.leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        CommRingCat.{v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X))).hom.app A ≫
        (TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A) = 𝟙 _ from
      Iso.hom_inv_id_app _ _]
  exact (congrArg (fun arrow =>
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} g).unit.app A ≫ arrow)
    ((TopCat.Sheaf.pushforward CommRingCat.{v} g).map_id _)).trans
      (Category.comp_id _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem constructedInverse_inv_component (A : Y.Sheaf CommRingCat.{v}) :
    (constructedInverse g A).inv =
      (TopCat.Sheaf.pullbackIso (Type v) g).hom.app ((underlyingSheaf Y).obj A) ≫
        (constructionComparisonIso g A).hom ≫
          (underlyingSheaf X).map ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A) := by
  simp only [constructedInverse, constructionComparisonIso,
    Iso.trans_inv, Functor.mapIso_inv]
  simp only [Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem canonicalComponent_eq_construction (A : Y.Sheaf CommRingCat.{v}) :
    canonicalComponent g A = (constructedInverse g A).inv := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _).injective
  rw [canonicalComponent_mate,
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv_unit,
    constructedInverse_inv_component, Functor.map_comp, Functor.map_comp]
  symm
  calc
    _ = (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          (Type v) (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app ((underlyingSheaf Y).obj A) ≫
        (TopCat.Sheaf.pushforward (Type v) g).map (constructionComparisonIso g A).hom ≫
          (TopCat.Sheaf.pushforward (Type v) g).map
            ((underlyingSheaf X).map ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A)) := by
            rw [← Category.assoc, abstractTypeUnit_toConstruction]
    _ = (underlyingSheaf Y).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
            CommRingCat.{v} (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app A) ≫
          (TopCat.Sheaf.pushforward (Type v) g).map
            ((underlyingSheaf X).map ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A)) := by
            rw [← Category.assoc, ← construction_unit_bridge]
    _ = (underlyingSheaf Y).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
              CommRingCat.{v} (Opens.grothendieckTopology Y)
              (Opens.grothendieckTopology X)).unit.app A ≫
            (TopCat.Sheaf.pushforward CommRingCat.{v} g).map
              ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A)) := by
            have commMap :
                (TopCat.Sheaf.pushforward (Type v) g).map
                    ((underlyingSheaf X).map
                      ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A)) =
                  (underlyingSheaf Y).map
                    ((TopCat.Sheaf.pushforward CommRingCat.{v} g).map
                      ((TopCat.Sheaf.pullbackIso CommRingCat.{v} g).inv.app A)) := by
              rfl
            rw [commMap]
            exact ((underlyingSheaf Y).map_comp _ _).symm
    _ = _ := congrArg (underlyingSheaf Y).map (abstractRingUnit_fromConstruction g A)

/-- The canonical component is invertible for every continuous map. -/
theorem canonicalComponent_isIso (A : Y.Sheaf CommRingCat.{v}) :
    IsIso (canonicalComponent g A) := by
  rw [canonicalComponent_eq_construction]
  infer_instance

/-- The natural isomorphism whose forward map is the canonical adjunction mate. -/
@[expose] noncomputable def canonicalComparisonIso :
    underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g ≅
      TopCat.Sheaf.pullback CommRingCat.{v} g ⋙ underlyingSheaf X :=
  NatIso.ofComponents (fun A =>
    @asIso _ _ _ _ (canonicalComponent g A) (canonicalComponent_isIso g A))
    (fun {_ _} a => canonicalComponent_naturality g a)

/-- The forward component of `canonicalComparisonIso` is the actual mate. -/
@[simp] theorem canonicalComparisonIso_hom_app (A : Y.Sheaf CommRingCat.{v}) :
    (canonicalComparisonIso g).hom.app A = canonicalComponent g A := rfl

/-- The inverse natural isomorphism, from underlying ring pullback to
pullback of the underlying sheaf. -/
noncomputable def inverseComparisonIso :
    TopCat.Sheaf.pullback CommRingCat.{v} g ⋙ underlyingSheaf X ≅
      underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g :=
  (canonicalComparisonIso g).symm

/-- The inverse of the reverse isomorphism recovers the canonical mate. -/
@[simp] theorem inverseComparisonIso_inv_app (A : Y.Sheaf CommRingCat.{v}) :
    (inverseComparisonIso g).inv.app A = canonicalComponent g A := by
  exact canonicalComparisonIso_hom_app g A

private theorem ringPullbackId_mate (Z : TopCat.{v}) (A : Z.Sheaf CommRingCat.{v}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} (𝟙 Z)).homEquiv _ _
      (TopCat.Sheaf.pullbackIdHom CommRingCat.{v} Z A) = 𝟙 A := by
  let adjDirect : TopCat.Sheaf.pullback CommRingCat.{v} (𝟙 Z) ⊣
      𝟭 (Z.Sheaf CommRingCat.{v}) :=
    TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} (𝟙 Z)
  change adjDirect.homEquiv A A
    ((Adjunction.leftAdjointUniq Adjunction.id adjDirect).inv.app A) = 𝟙 A
  rw [Adjunction.leftAdjointUniq_inv_app]
  simpa using (Adjunction.homEquiv_leftAdjointUniq_hom_app adjDirect Adjunction.id A)

private theorem typePullbackId_mate (Z : TopCat.{v}) (A : Z.Sheaf (Type v)) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (𝟙 Z)).homEquiv _ _
      (TopCat.Sheaf.pullbackIdHom (Type v) Z A) = 𝟙 A := by
  let adjDirect : TopCat.Sheaf.pullback (Type v) (𝟙 Z) ⊣
      𝟭 (Z.Sheaf (Type v)) :=
    TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (𝟙 Z)
  change adjDirect.homEquiv A A
    ((Adjunction.leftAdjointUniq Adjunction.id adjDirect).inv.app A) = 𝟙 A
  rw [Adjunction.leftAdjointUniq_inv_app]
  simpa using (Adjunction.homEquiv_leftAdjointUniq_hom_app adjDirect Adjunction.id A)

/-- Compatibility with the native identity-pullback map. -/
theorem canonicalComponent_id (Z : TopCat.{v}) (A : Z.Sheaf CommRingCat.{v}) :
    canonicalComponent (𝟙 Z) A ≫
        (underlyingSheaf Z).map (TopCat.Sheaf.pullbackIdHom CommRingCat.{v} Z A) =
      TopCat.Sheaf.pullbackIdHom (Type v) Z ((underlyingSheaf Z).obj A) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (𝟙 Z)).homEquiv _ _).injective
  rw [canonicalComponent_mate_map, ringPullbackId_mate, typePullbackId_mate]
  exact (underlyingSheaf Z).map_id A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with native composition of pullbacks. -/
theorem canonicalComponent_comp {Z : TopCat.{v}}
    (f : X ⟶ Y) (h : Y ⟶ Z) (A : Z.Sheaf CommRingCat.{v}) :
    (TopCat.Sheaf.pullback (Type v) f).map (canonicalComponent h A) ≫
        canonicalComponent f ((TopCat.Sheaf.pullback CommRingCat.{v} h).obj A) ≫
          (underlyingSheaf X).map (TopCat.Sheaf.pullbackCompHom CommRingCat.{v} f h A) =
      TopCat.Sheaf.pullbackCompHom (Type v) f h ((underlyingSheaf Z).obj A) ≫
        canonicalComponent (f ≫ h) A := by
  let adjComp := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) h).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
  let adjDirect := TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (f ≫ h)
  let adjCompAdd := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} h).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f)
  let adjDirectAdd := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} (f ≫ h)
  have ringComparison_mate :
      adjCompAdd.homEquiv A ((TopCat.Sheaf.pullback CommRingCat.{v} (f ≫ h)).obj A)
        (TopCat.Sheaf.pullbackCompHom CommRingCat.{v} f h A) =
        adjDirectAdd.unit.app A := by
    change adjCompAdd.homEquiv A ((TopCat.Sheaf.pullback CommRingCat.{v} (f ≫ h)).obj A)
      ((Adjunction.leftAdjointUniq adjCompAdd adjDirectAdd).hom.app A) = _
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app adjCompAdd adjDirectAdd A
  have typeComparison_mate :
      adjComp.homEquiv ((underlyingSheaf Z).obj A)
          ((TopCat.Sheaf.pullback (Type v) (f ≫ h)).obj ((underlyingSheaf Z).obj A))
        (TopCat.Sheaf.pullbackCompHom (Type v) f h ((underlyingSheaf Z).obj A)) =
        adjDirect.unit.app ((underlyingSheaf Z).obj A) := by
    change adjComp.homEquiv _ _
      ((Adjunction.leftAdjointUniq adjComp adjDirect).hom.app ((underlyingSheaf Z).obj A)) = _
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app adjComp adjDirect _
  have right_mate :
      adjComp.homEquiv _ _
        (TopCat.Sheaf.pullbackCompHom (Type v) f h ((underlyingSheaf Z).obj A) ≫
          canonicalComponent (f ≫ h) A) =
        (underlyingSheaf Z).map (adjDirectAdd.unit.app A) := by
    rw [adjComp.homEquiv_naturality_right, typeComparison_mate]
    change adjDirect.unit.app ((underlyingSheaf Z).obj A) ≫
      (TopCat.Sheaf.pushforward (Type v) (f ≫ h)).map (canonicalComponent (f ≫ h) A) = _
    calc
      _ = adjDirect.homEquiv _ _ (canonicalComponent (f ≫ h) A) := by
        exact (adjDirect.homEquiv_unit (f := canonicalComponent (f ≫ h) A)).symm
      _ = _ := canonicalComponent_mate (f ≫ h) A
  have left_mate :
      adjComp.homEquiv _ _
        ((TopCat.Sheaf.pullback (Type v) f).map (canonicalComponent h A) ≫
          canonicalComponent f ((TopCat.Sheaf.pullback CommRingCat.{v} h).obj A) ≫
            (underlyingSheaf X).map (TopCat.Sheaf.pullbackCompHom CommRingCat.{v} f h A)) =
        (underlyingSheaf Z).map (adjDirectAdd.unit.app A) := by
    rw [Adjunction.comp_homEquiv]
    change (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) h).homEquiv _ _
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv _ _
        ((TopCat.Sheaf.pullback (Type v) f).map (canonicalComponent h A) ≫
          canonicalComponent f ((TopCat.Sheaf.pullback CommRingCat.{v} h).obj A) ≫
            (underlyingSheaf X).map (TopCat.Sheaf.pullbackCompHom CommRingCat.{v} f h A))) = _
    rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv_naturality_left,
      canonicalComponent_mate_map]
    calc
      _ = (underlyingSheaf Z).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} h).homEquiv A _
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{v} f).homEquiv _ _
              (TopCat.Sheaf.pullbackCompHom CommRingCat.{v} f h A))) := by
            exact canonicalComponent_mate_map h A _ _
      _ = (underlyingSheaf Z).map
          (adjCompAdd.homEquiv A ((TopCat.Sheaf.pullback CommRingCat.{v} (f ≫ h)).obj A)
            (TopCat.Sheaf.pullbackCompHom CommRingCat.{v} f h A)) := by
          rw [Adjunction.comp_homEquiv]
          rfl
      _ = _ := congrArg (underlyingSheaf Z).map ringComparison_mate
  apply (adjComp.homEquiv _ _).injective
  exact left_mate.trans right_mate.symm


end TopCat.Sheaf.CommRingForget
