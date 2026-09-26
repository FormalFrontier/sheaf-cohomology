/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Topology.Sheaves.Flasque
public import SheafCohomology.CompactOpenSections

public section

/-!
# Quasi-flasque sheaves

A sheaf valued in a category is quasi-flasque when its global sections
restrict epimorphically to every quasi-compact open.  This recovers the usual
surjectivity condition for sheaves of types and the standard condition for
abelian sheaves.  This file establishes filtered-colimit stability in both
settings on compact prespectral, quasi-separated spaces.

Unlike flasqueness, quasi-flasqueness only controls restrictions from the
terminal open.  No cohomological acyclicity statement is made here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace

universe u v

namespace TopCat.Sheaf

variable {X : Type u} [TopologicalSpace X]
variable {C : Type (v + 1)} [Category.{v} C]

/-- Restriction from global sections to sections on `U`. -/
abbrev restriction (U : Opens X) :
    SheafCohomology.CompactOpenSections.sectionsOf (X := X) (C := C)
        (⊤ : Opens X) ⟶
      SheafCohomology.CompactOpenSections.sectionsOf (X := X) (C := C) U :=
  (CategoryTheory.sheafSections
    (Opens.grothendieckTopology X) C).map
      (homOfLE le_top).op

/-- A sheaf is quasi-flasque if global sections restrict
epimorphically to every compact open. -/
class IsQuasiFlasque
    (F : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) C) : Prop where
  epi_restriction (U : Opens X) (hU : IsCompact (U : Set X)) :
    Epi ((restriction U).app F)

namespace IsQuasiFlasque

/-- Every flasque sheaf is quasi-flasque. -/
instance of_isFlasque
  (F : TopCat.Sheaf C (TopCat.of X))
    [IsFlasque F] : IsQuasiFlasque F where
  epi_restriction U _hU := by
    dsimp [restriction, SheafCohomology.CompactOpenSections.sectionsOf]
    change Epi (F.obj.map (homOfLE le_top).op)
    infer_instance

omit [Category.{v} C] in
/-- For a sheaf of types, quasi-flasqueness is exactly surjectivity of every
restriction from the terminal open to a compact open. -/
theorem iff_surjective
    (F : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) (Type u)) :
    IsQuasiFlasque F ↔
      ∀ (U : Opens X) (_hU : IsCompact (U : Set X)),
        Function.Surjective ((restriction U).app F) := by
  constructor
  · intro h U hU
    rw [← CategoryTheory.epi_iff_surjective]
    exact h.epi_restriction U hU
  · intro h
    constructor
    intro U hU
    rw [CategoryTheory.epi_iff_surjective]
    exact h U hU

variable [UnivLE.{u, v}]
variable [HasWeakSheafify
  (Opens.grothendieckTopology X) C]
variable {FC : C → C → Type*} {CC : C → Type v}
variable [∀ A B, FunLike (FC A B) (CC A) (CC B)]
variable [instCC : ConcreteCategory C FC] [HasColimitsOfSize.{v, v} C]
variable [HasLimitsOfSize.{u, u} C]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
variable [instReflectsIsomorphisms :
  (CategoryTheory.forget C).ReflectsIsomorphisms]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective
  C]
variable {I : Type v} [SmallCategory I] [IsFiltered I]
variable (F : I ⥤ CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) C)

omit [UnivLE.{u, v}] [HasLimitsOfSize.{u, u} C] in
/-- The canonical colimit comparison is natural with respect to restriction
from the terminal open to `U`. -/
@[reassoc]
theorem colimit_map_restriction_comp_post (U : Opens X) :
    colimMap (Functor.whiskerLeft F (restriction U)) ≫
        colimit.post F (SheafCohomology.CompactOpenSections.sectionsOf U) =
      colimit.post F
          (SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens X)) ≫
        (restriction U).app (colimit F) := by
  apply colimit.hom_ext
  intro i
  simp

omit [UnivLE.{u, v}] in
include instCC instReflectsIsomorphisms in
/-- On a compact prespectral, quasi-separated space, a filtered colimit of
quasi-flasque sheaves is quasi-flasque. -/
theorem isQuasiFlasque_colimit
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    [∀ i, IsQuasiFlasque (F.obj i)] : IsQuasiFlasque (colimit F) := by
  constructor
  intro U hU
  let _ : PreservesColimit F
      (SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens X)) :=
    SheafCohomology.CompactOpenSections.preservesColimit_globalSections F
  let _ : PreservesColimit F
      (SheafCohomology.CompactOpenSections.sectionsOf U) :=
    SheafCohomology.CompactOpenSections.preservesColimit_sections F U hU
  let _ : ∀ i, Epi
      ((Functor.whiskerLeft F (restriction U)).app i) := fun i =>
    IsQuasiFlasque.epi_restriction (F := F.obj i) U hU
  let _ : Epi (Functor.whiskerLeft F (restriction U)) :=
    NatTrans.epi_of_epi_app _
  let _ : Epi (colimMap (Functor.whiskerLeft F (restriction U))) := by
    infer_instance
  let hcomp : Epi
      (colimMap (Functor.whiskerLeft F (restriction U)) ≫
        colimit.post F (SheafCohomology.CompactOpenSections.sectionsOf U)) := by
    infer_instance
  let _ : Epi
      (colimit.post F
          (SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens X)) ≫
        (restriction U).app (colimit F)) :=
    colimit_map_restriction_comp_post F U ▸ hcomp
  exact CategoryTheory.epi_of_epi
    (colimit.post F
      (SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens X)))
    ((restriction U).app (colimit F))

end IsQuasiFlasque

end TopCat.Sheaf
