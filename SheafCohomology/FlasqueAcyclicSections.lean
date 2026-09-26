/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.FlasqueAcyclicResolution

public section

/-!
# The Ext-zero complex of the flasque resolution

This file identifies the degree-zero Ext complex underlying the packaged
flasque acyclic resolution with the complex of sections on the terminal open.
The identification is natural in the input sheaf.

The construction has the same small-universe boundary as the functorial
flasque resolution and its acyclic-resolution packaging.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}
variable [CompactSpace X] [QuasiSeparatedSpace X] [PrespectralSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [HasExt (CategoryTheory.Sheaf
  (Opens.grothendieckTopology X) AddCommGrpCat)]

/-- A sheaf morphism induces the corresponding map between the complexes of
terminal-open sections of their functorial flasque resolutions. -/
noncomputable abbrev flasqueResolutionSectionsMap
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    flasqueResolutionSections F ⟶ flasqueResolutionSections G :=
  ((SheafCohomology.CompactOpenSections.sections
    (⊤ : Opens X)).mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((flasqueResolutionNat (X := X)).asFunctor.map f)

/-- A sheaf morphism induces the corresponding map between the degree-zero
Ext complexes of their packaged flasque acyclic resolutions. -/
noncomputable abbrev flasqueAcyclicResolutionExtZeroComplexMap
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    (flasqueAcyclicResolution F).extZeroComplex ⟶
      (flasqueAcyclicResolution G).extZeroComplex :=
  ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) 0).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
        ((flasqueResolutionNat (X := X)).asFunctor.map f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma flasqueAcyclicResolutionExtZeroComplexMap_eq
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    flasqueAcyclicResolutionExtZeroComplexMap f =
      (flasqueAcyclicResolution F).extZeroComplexMap
        (flasqueAcyclicResolution G) (flasqueAcyclicResolutionHom f).hom :=
  rfl

/-- The degree-zero Ext complex of the packaged flasque acyclic resolution is
canonically the complex of its terminal-open sections. -/
@[expose] noncomputable def flasqueAcyclicResolutionExtZeroComplexIsoSections
    (F : Sheaf AddCommGrpCat X) :
    (flasqueAcyclicResolution F).extZeroComplex ≅
      flasqueResolutionSections F :=
  (NatIso.mapHomologicalComplex
    (SheafCohomology.DegreeZero.functorHZeroIsoSections (X := X))
    (ComplexShape.up ℕ)).app (flasqueResolution F)

@[reassoc]
lemma flasqueAcyclicResolutionExtZeroComplexIsoSections_hom_naturality
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) :
    flasqueAcyclicResolutionExtZeroComplexMap f ≫
        (flasqueAcyclicResolutionExtZeroComplexIsoSections G).hom =
      (flasqueAcyclicResolutionExtZeroComplexIsoSections F).hom ≫
        flasqueResolutionSectionsMap f :=
  (NatIso.mapHomologicalComplex
    (SheafCohomology.DegreeZero.functorHZeroIsoSections (X := X))
    (ComplexShape.up ℕ)).hom.naturality
      ((flasqueResolutionNat (X := X)).asFunctor.map f)

/-- The induced identification of the homology of the degree-zero Ext complex
with the homology of terminal-open sections. -/
@[expose] noncomputable def flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology
    (F : Sheaf AddCommGrpCat X) (q : ℕ) :
    (flasqueAcyclicResolution F).extZeroComplex.homology q ≅
      (flasqueResolutionSections F).homology q :=
  HomologicalComplex.homologyMapIso
    (flasqueAcyclicResolutionExtZeroComplexIsoSections F) q

@[reassoc]
lemma flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology_hom_naturality
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G) (q : ℕ) :
    HomologicalComplex.homologyMap
          (flasqueAcyclicResolutionExtZeroComplexMap f) q ≫
        (flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology G q).hom =
      (flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology F q).hom ≫
        HomologicalComplex.homologyMap (flasqueResolutionSectionsMap f) q := by
  change
    HomologicalComplex.homologyMap
        (flasqueAcyclicResolutionExtZeroComplexMap f) q ≫
      HomologicalComplex.homologyMap
        (flasqueAcyclicResolutionExtZeroComplexIsoSections G).hom q =
    HomologicalComplex.homologyMap
        (flasqueAcyclicResolutionExtZeroComplexIsoSections F).hom q ≫
      HomologicalComplex.homologyMap (flasqueResolutionSectionsMap f) q
  rw [← HomologicalComplex.homologyMap_comp,
    flasqueAcyclicResolutionExtZeroComplexIsoSections_hom_naturality,
    HomologicalComplex.homologyMap_comp]

end TopCat.Sheaf
