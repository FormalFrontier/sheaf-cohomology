/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import SheafCohomology.AbelianForget.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import SheafCohomology.PullbackCoherence

public section

/-!
# Forgetting abelian sheaves and pullback

The comparison is the native Type-valued pullback/pushforward mate of the
forgotten additive unit. It is an isomorphism for every continuous map.
-/

set_option warningAsError true

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

namespace TopCat.Sheaf.AbelianForget

variable {X Y : TopCat.{v}} (g : X ⟶ Y)
/-- The comparison from pullback of the underlying sheaf to the underlying
additive pullback, defined as the native Type-valued adjunction mate of the
forgotten additive unit. -/
noncomputable def canonicalComponent (A : Y.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pullback (Type v) g).obj ((underlyingSheaf Y).obj A) ⟶
      (underlyingSheaf X).obj ((TopCat.Sheaf.pullback AddCommGrpCat.{v} g).obj A) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _).symm
    ((underlyingSheaf Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A))

/-- The canonical comparison is the mate of the forgotten additive unit. -/
theorem canonicalComponent_mate (A : Y.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _
      (canonicalComponent g A) =
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A) := by
  exact Equiv.apply_symm_apply _ _

/-- The mate law for an arbitrary morphism out of the additive pullback. -/
theorem canonicalComponent_mate_map (A : Y.Sheaf AddCommGrpCat.{v})
    (B : X.Sheaf AddCommGrpCat.{v})
    (a : (TopCat.Sheaf.pullback AddCommGrpCat.{v} g).obj A ⟶ B) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _
      (canonicalComponent g A ≫ (underlyingSheaf X).map a) =
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).homEquiv A B a) := by
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv_naturality_right,
    canonicalComponent_mate]
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).homEquiv_unit]
  change (underlyingSheaf Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A) ≫
      (underlyingSheaf Y).map ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} g).map a) =
    (underlyingSheaf Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{v} g).map a)
  exact ((underlyingSheaf Y).map_comp _ _).symm

/-- Naturality of the pullback/forgetful comparison. -/
theorem canonicalComponent_naturality {A B : Y.Sheaf AddCommGrpCat.{v}}
    (a : A ⟶ B) :
    (TopCat.Sheaf.pullback (Type v) g).map ((underlyingSheaf Y).map a) ≫
      canonicalComponent g B =
      canonicalComponent g A ≫
        (underlyingSheaf X).map ((TopCat.Sheaf.pullback AddCommGrpCat.{v} g).map a) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv _ _).injective
  rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv_naturality_left,
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) g).homEquiv_naturality_right,
    canonicalComponent_mate, canonicalComponent_mate]
  change (underlyingSheaf Y).map a ≫
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app B) =
    (underlyingSheaf Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A) ≫
      (underlyingSheaf Y).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} g).map
          ((TopCat.Sheaf.pullback AddCommGrpCat.{v} g).map a))
  rw [← (underlyingSheaf Y).map_comp, ← (underlyingSheaf Y).map_comp]
  exact congrArg (underlyingSheaf Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.naturality a)

/-- The natural transformation whose components are native adjunction mates. -/
@[expose] noncomputable def canonicalComparison :
    underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g ⟶
      TopCat.Sheaf.pullback AddCommGrpCat.{v} g ⋙ underlyingSheaf X where
  app := canonicalComponent g
  naturality := by
    intro A B a
    exact canonicalComponent_naturality g a

/-- The component of the natural transformation is the native mate. -/
@[simp] theorem canonicalComparison_app (A : Y.Sheaf AddCommGrpCat.{v}) :
    (canonicalComparison g).app A = canonicalComponent g A := rfl

private noncomputable def presheafPullbackForgetIso :
    TopCat.Presheaf.pullback AddCommGrpCat.{v} g ⋙
      (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{v}) ≅
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{v}) ⋙
      TopCat.Presheaf.pullback (Type v) g := by
  let : CategoryTheory.RepresentablyFlat (Opens.map g) :=
    CategoryTheory.flat_of_preservesFiniteLimits (Opens.map g)
  exact Functor.lanCompIsoOfPreserves (CategoryTheory.forget AddCommGrpCat.{v}) (Opens.map g).op

private theorem presheafPullbackForget_unit (P : Y.Presheaf AddCommGrpCat.{v}) :
    ((Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{v})).map
        ((Opens.map g).op.lanUnit.app P) =
      (Opens.map g).op.lanUnit.app (P ⋙ (CategoryTheory.forget AddCommGrpCat.{v})) ≫
        ((Functor.whiskeringLeft _ _ _).obj (Opens.map g).op).map
          ((presheafPullbackForgetIso g).app P).inv := by
  exact (Functor.leftKanExtensionCompIsoOfPreserves_inv_fac
    (CategoryTheory.forget AddCommGrpCat.{v}) P (Opens.map g).op).symm

private noncomputable def localSheafifyForgetIso (P : X.Presheaf AddCommGrpCat.{v}) :
    (presheafToSheaf (Opens.grothendieckTopology X) (Type v)).obj
        (P ⋙ (CategoryTheory.forget AddCommGrpCat.{v})) ≅
      (underlyingSheaf X).obj
        ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj P) :=
  (sheafComposeNatIso (Opens.grothendieckTopology X)
      (CategoryTheory.forget AddCommGrpCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v})
      (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v))).app P

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem sheafification_unit_bridge (Q : X.Presheaf AddCommGrpCat.{v})
    (R : X.Presheaf (Type v)) (ρ : Q ⋙ CategoryTheory.forget AddCommGrpCat.{v} ≅ R) :
    (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)).unit.app R ≫
        (TopCat.Sheaf.forget (Type v) X).map
          ((presheafToSheaf (Opens.grothendieckTopology X) (Type v)).mapIso ρ).inv ≫
        (TopCat.Sheaf.forget (Type v) X).map (localSheafifyForgetIso Q).hom =
      ρ.inv ≫ whiskerRight
        ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v}).unit.app Q)
          (CategoryTheory.forget AddCommGrpCat.{v}) := by
  have hUnit := (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)).unit.naturality ρ.inv
  have hCompose := sheafComposeNatTrans_fac (Opens.grothendieckTopology X)
    (CategoryTheory.forget AddCommGrpCat.{v})
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v})
    (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)) Q
  calc
    _ = ρ.inv ≫
        (sheafificationAdjunction (Opens.grothendieckTopology X) (Type v)).unit.app
          (Q ⋙ CategoryTheory.forget AddCommGrpCat.{v}) ≫
        (TopCat.Sheaf.forget (Type v) X).map (localSheafifyForgetIso Q).hom := by
          rw [← Category.assoc]
          exact congrArg (fun arrow => arrow ≫ (TopCat.Sheaf.forget (Type v) X).map
            (localSheafifyForgetIso Q).hom) hUnit.symm
    _ = _ := by
      exact congrArg (fun arrow => ρ.inv ≫ arrow) hCompose

private noncomputable def constructionComparisonIso (A : Y.Sheaf AddCommGrpCat.{v}) :
    (Functor.sheafPullbackConstruction.sheafPullback (Opens.map g) (Type v)
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj
        ((underlyingSheaf Y).obj A) ≅
      (underlyingSheaf X).obj
        ((Functor.sheafPullbackConstruction.sheafPullback (Opens.map g) AddCommGrpCat.{v}
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj A) :=
  ((presheafToSheaf (Opens.grothendieckTopology X) (Type v)).mapIso
    ((presheafPullbackForgetIso g).app ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A))).symm ≪≫
      localSheafifyForgetIso
        ((TopCat.Presheaf.pullback AddCommGrpCat.{v} g).obj
          ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A))

private noncomputable def constructedInverse (A : Y.Sheaf AddCommGrpCat.{v}) :
    (underlyingSheaf X).obj ((TopCat.Sheaf.pullback AddCommGrpCat.{v} g).obj A) ≅
      (TopCat.Sheaf.pullback (Type v) g).obj ((underlyingSheaf Y).obj A) :=
  (underlyingSheaf X).mapIso ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).app A) ≪≫
    (localSheafifyForgetIso
      ((TopCat.Presheaf.pullback AddCommGrpCat.{v} g).obj
        ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A))).symm ≪≫
    (presheafToSheaf (Opens.grothendieckTopology X) (Type v)).mapIso
      ((presheafPullbackForgetIso g).app
        ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A)) ≪≫
    ((TopCat.Sheaf.pullbackIso (Type v) g).app ((underlyingSheaf Y).obj A)).symm

private theorem constructedAddUnit_forget (A : Y.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} Y).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          AddCommGrpCat.{v} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app A) =
      (((Opens.map g).op.lanAdjunction AddCommGrpCat.{v}).comp
        (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v})).unit.app
          ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A) := by
  let adj := ((Opens.map g).op.lanAdjunction AddCommGrpCat.{v}).comp
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v})
  let commRight :
      𝟭 (X.Sheaf AddCommGrpCat.{v}) ⋙
          sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} ⋙
            (Functor.whiskeringLeft _ _ _).obj (Opens.map g).op ≅
        TopCat.Sheaf.pushforward AddCommGrpCat.{v} g ⋙
          sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v} := Iso.refl _
  let commLeft :
      sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v} ⋙
          (Opens.map g).op.lan ⋙
            presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v} ≅
        Functor.sheafPullbackConstruction.sheafPullback (Opens.map g) AddCommGrpCat.{v}
            (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) ⋙
          𝟭 (X.Sheaf AddCommGrpCat.{v}) := Iso.refl _
  have unit_eq := adj.map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v})
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
private theorem construction_unit_bridge (A : Y.Sheaf AddCommGrpCat.{v}) :
    (underlyingSheaf Y).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          AddCommGrpCat.{v} (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app A) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
          (Type v) (Opens.grothendieckTopology Y)
          (Opens.grothendieckTopology X)).unit.app ((underlyingSheaf Y).obj A) ≫
        (TopCat.Sheaf.pushforward (Type v) g).map ((constructionComparisonIso g A).hom) := by
  apply (TopCat.Sheaf.forget (Type v) Y).map_injective
  change ((Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{v})).map
    ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        AddCommGrpCat.{v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app A)) =
    (TopCat.Sheaf.forget (Type v) Y).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        (Type v) (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app ((underlyingSheaf Y).obj A)) ≫
      ((Functor.whiskeringLeft _ _ _).obj (Opens.map g).op).map
        ((TopCat.Sheaf.forget (Type v) X).map ((constructionComparisonIso g A).hom))
  rw [constructedAddUnit_forget, constructedTypeUnit_forget]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  rw [Functor.map_comp]
  simp only [constructionComparisonIso, Iso.trans_hom, Iso.symm_hom]
  rw [Functor.map_comp, Functor.map_comp]
  rw [Functor.lanAdjunction_unit, Functor.lanAdjunction_unit]
  rw [presheafPullbackForget_unit]
  change ((Opens.map g).op.lanUnit.app
      (((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A) ⋙ CategoryTheory.forget AddCommGrpCat.{v}) ≫
        whiskerLeft (Opens.map g).op
          ((presheafPullbackForgetIso g).app
            ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A)).inv) ≫
      whiskerLeft (Opens.map g).op
        (whiskerRight
          ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{v}).unit.app
            ((Opens.map g).op.lan.obj
              ((TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A)))
          (CategoryTheory.forget AddCommGrpCat.{v})) = _
  let P := (TopCat.Sheaf.forget AddCommGrpCat.{v} Y).obj A
  let Q := ((Opens.map g).op.lan).obj P
  let R := ((Opens.map g).op.lan).obj (P ⋙ CategoryTheory.forget AddCommGrpCat.{v})
  let rho := (presheafPullbackForgetIso g).app P
  have hSheaf := sheafification_unit_bridge Q R rho
  convert congrArg (fun arrow =>
    (Opens.map g).op.lanUnit.app (P ⋙ CategoryTheory.forget AddCommGrpCat.{v}) ≫
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
private theorem abstractAddUnit_fromConstruction (A : Y.Sheaf AddCommGrpCat.{v}) :
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        AddCommGrpCat.{v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X)).unit.app A ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{v} g).map
        ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A) =
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A := by
  have unit_eq := Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
      AddCommGrpCat.{v} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) A
  rw [← unit_eq, Category.assoc, ← Functor.map_comp,
    show ((Adjunction.leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
        AddCommGrpCat.{v} (Opens.grothendieckTopology Y)
        (Opens.grothendieckTopology X))).hom.app A ≫
        (TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A) = 𝟙 _ from
      Iso.hom_inv_id_app _ _]
  exact (congrArg (fun arrow =>
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} g).unit.app A ≫ arrow)
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} g).map_id _)).trans
      (Category.comp_id _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem constructedInverse_inv_component (A : Y.Sheaf AddCommGrpCat.{v}) :
    (constructedInverse g A).inv =
      (TopCat.Sheaf.pullbackIso (Type v) g).hom.app ((underlyingSheaf Y).obj A) ≫
        (constructionComparisonIso g A).hom ≫
          (underlyingSheaf X).map ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A) := by
  simp only [constructedInverse, constructionComparisonIso,
    Iso.trans_inv, Functor.mapIso_inv]
  simp only [Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Category.assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem canonicalComponent_eq_construction (A : Y.Sheaf AddCommGrpCat.{v}) :
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
            ((underlyingSheaf X).map ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A)) := by
            rw [← Category.assoc, abstractTypeUnit_toConstruction]
    _ = (underlyingSheaf Y).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
            AddCommGrpCat.{v} (Opens.grothendieckTopology Y)
            (Opens.grothendieckTopology X)).unit.app A) ≫
          (TopCat.Sheaf.pushforward (Type v) g).map
            ((underlyingSheaf X).map ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A)) := by
            rw [← Category.assoc, ← construction_unit_bridge]
    _ = (underlyingSheaf Y).map
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map g)
              AddCommGrpCat.{v} (Opens.grothendieckTopology Y)
              (Opens.grothendieckTopology X)).unit.app A ≫
            (TopCat.Sheaf.pushforward AddCommGrpCat.{v} g).map
              ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A)) := by
            have commMap :
                (TopCat.Sheaf.pushforward (Type v) g).map
                    ((underlyingSheaf X).map
                      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A)) =
                  (underlyingSheaf Y).map
                    ((TopCat.Sheaf.pushforward AddCommGrpCat.{v} g).map
                      ((TopCat.Sheaf.pullbackIso AddCommGrpCat.{v} g).inv.app A)) := by
              rfl
            rw [commMap]
            exact ((underlyingSheaf Y).map_comp _ _).symm
    _ = _ := congrArg (underlyingSheaf Y).map (abstractAddUnit_fromConstruction g A)

/-- The canonical component is invertible for every continuous map. -/
theorem canonicalComponent_isIso (A : Y.Sheaf AddCommGrpCat.{v}) :
    IsIso (canonicalComponent g A) := by
  rw [canonicalComponent_eq_construction]
  infer_instance

/-- The natural isomorphism whose forward map is the canonical adjunction mate. -/
@[expose] noncomputable def canonicalComparisonIso :
    underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g ≅
      TopCat.Sheaf.pullback AddCommGrpCat.{v} g ⋙ underlyingSheaf X :=
  NatIso.ofComponents (fun A =>
    @asIso _ _ _ _ (canonicalComponent g A) (canonicalComponent_isIso g A))
    (fun {_ _} a => canonicalComponent_naturality g a)

/-- The forward component of `canonicalComparisonIso` is the actual mate. -/
@[simp] theorem canonicalComparisonIso_hom_app (A : Y.Sheaf AddCommGrpCat.{v}) :
    (canonicalComparisonIso g).hom.app A = canonicalComponent g A := rfl

/-- The inverse natural isomorphism, from underlying additive pullback to
pullback of the underlying sheaf. -/
noncomputable def inverseComparisonIso :
    TopCat.Sheaf.pullback AddCommGrpCat.{v} g ⋙ underlyingSheaf X ≅
      underlyingSheaf Y ⋙ TopCat.Sheaf.pullback (Type v) g :=
  (canonicalComparisonIso g).symm

/-- The inverse of the reverse isomorphism recovers the canonical mate. -/
@[simp] theorem inverseComparisonIso_inv_app (A : Y.Sheaf AddCommGrpCat.{v}) :
    (inverseComparisonIso g).inv.app A = canonicalComponent g A := by
  exact canonicalComparisonIso_hom_app g A

private theorem additivePullbackId_mate (Z : TopCat.{v}) (A : Z.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} (𝟙 Z)).homEquiv _ _
      (TopCat.Sheaf.pullbackIdHom AddCommGrpCat.{v} Z A) = 𝟙 A := by
  let adjDirect : TopCat.Sheaf.pullback AddCommGrpCat.{v} (𝟙 Z) ⊣
      𝟭 (Z.Sheaf AddCommGrpCat.{v}) :=
    TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} (𝟙 Z)
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
theorem canonicalComponent_id (Z : TopCat.{v}) (A : Z.Sheaf AddCommGrpCat.{v}) :
    canonicalComponent (𝟙 Z) A ≫
        (underlyingSheaf Z).map (TopCat.Sheaf.pullbackIdHom AddCommGrpCat.{v} Z A) =
      TopCat.Sheaf.pullbackIdHom (Type v) Z ((underlyingSheaf Z).obj A) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (𝟙 Z)).homEquiv _ _).injective
  rw [canonicalComponent_mate_map, additivePullbackId_mate, typePullbackId_mate]
  exact (underlyingSheaf Z).map_id A

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with native composition of pullbacks. -/
theorem canonicalComponent_comp {Z : TopCat.{v}}
    (f : X ⟶ Y) (h : Y ⟶ Z) (A : Z.Sheaf AddCommGrpCat.{v}) :
    (TopCat.Sheaf.pullback (Type v) f).map (canonicalComponent h A) ≫
        canonicalComponent f ((TopCat.Sheaf.pullback AddCommGrpCat.{v} h).obj A) ≫
          (underlyingSheaf X).map (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} f h A) =
      TopCat.Sheaf.pullbackCompHom (Type v) f h ((underlyingSheaf Z).obj A) ≫
        canonicalComponent (f ≫ h) A := by
  let adjComp := (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) h).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f)
  let adjDirect := TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) (f ≫ h)
  let adjCompAdd := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} h).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f)
  let adjDirectAdd := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} (f ≫ h)
  have additiveComparison_mate :
      adjCompAdd.homEquiv A ((TopCat.Sheaf.pullback AddCommGrpCat.{v} (f ≫ h)).obj A)
        (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} f h A) =
        adjDirectAdd.unit.app A := by
    change adjCompAdd.homEquiv A ((TopCat.Sheaf.pullback AddCommGrpCat.{v} (f ≫ h)).obj A)
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
          canonicalComponent f ((TopCat.Sheaf.pullback AddCommGrpCat.{v} h).obj A) ≫
            (underlyingSheaf X).map (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} f h A)) =
        (underlyingSheaf Z).map (adjDirectAdd.unit.app A) := by
    rw [Adjunction.comp_homEquiv]
    change (TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) h).homEquiv _ _
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv _ _
        ((TopCat.Sheaf.pullback (Type v) f).map (canonicalComponent h A) ≫
          canonicalComponent f ((TopCat.Sheaf.pullback AddCommGrpCat.{v} h).obj A) ≫
            (underlyingSheaf X).map (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} f h A))) = _
    rw [(TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f).homEquiv_naturality_left,
      canonicalComponent_mate_map]
    calc
      _ = (underlyingSheaf Z).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} h).homEquiv A _
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{v} f).homEquiv _ _
              (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} f h A))) := by
            exact canonicalComponent_mate_map h A _ _
      _ = (underlyingSheaf Z).map
          (adjCompAdd.homEquiv A ((TopCat.Sheaf.pullback AddCommGrpCat.{v} (f ≫ h)).obj A)
            (TopCat.Sheaf.pullbackCompHom AddCommGrpCat.{v} f h A)) := by
          rw [Adjunction.comp_homEquiv]
          rfl
      _ = _ := congrArg (underlyingSheaf Z).map additiveComparison_mate
  apply (adjComp.homEquiv _ _).injective
  exact left_mate.trans right_mate.symm


end TopCat.Sheaf.AbelianForget
