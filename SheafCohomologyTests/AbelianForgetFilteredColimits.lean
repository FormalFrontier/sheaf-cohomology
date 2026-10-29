/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
import SheafCohomology

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat.Sheaf.AbelianForget

namespace SheafCohomologyExamples.AbelianForgetFilteredColimitsClient

/-- The public preservation result applies to directed natural-number diagrams. -/
private theorem preserves_nat (Z : TopCat.{0}) :
    PreservesColimitsOfShape ℕ (underlyingSheaf Z) :=
  preservesFilteredColimits Z

/-- Native sheafification provides additive colimits without added instances. -/
private theorem native_additive_colimit (Z : TopCat.{0})
    (D : ℕ ⥤ Z.Sheaf AddCommGrpCat.{0}) : HasColimit D :=
  (CategoryTheory.Sheaf.instHasColimitsOfShape (J := Opens.grothendieckTopology Z)
    (D := AddCommGrpCat.{0}) (K := ℕ)).has_colimit D

/-- Filtered colimit preservation transports additive colimit existence to Type-valued sheaves. -/
private theorem native_underlying_colimit (Z : TopCat.{0})
    (D : ℕ ⥤ Z.Sheaf AddCommGrpCat.{0}) :
    HasColimit (D ⋙ underlyingSheaf Z) := by
  obtain ⟨w⟩ := (native_additive_colimit Z D).exists_colimit
  let : PreservesColimit D (underlyingSheaf Z) :=
    (preserves_nat Z).preservesColimit
  exact HasColimit.mk' ⟨{
    cocone := (underlyingSheaf Z).mapCocone w.cocone
    isColimit := isColimitOfPreserves (underlyingSheaf Z) w.isColimit }⟩

/-- The native stage-leg identity applies to filtered natural-number diagrams. -/
private theorem stage_nat (Z : TopCat.{0}) (D : ℕ ⥤ Z.Sheaf AddCommGrpCat.{0})
    [HasColimit D] [HasColimit (D ⋙ underlyingSheaf Z)] (stage : ℕ) :
    colimit.ι (D ⋙ underlyingSheaf Z) stage ≫ colimit.post D (underlyingSheaf Z) =
      (underlyingSheaf Z).map (colimit.ι D stage) :=
  canonicalComparison_stage Z D stage

/-- The literal native colimit comparison is invertible over any space. -/
private theorem iso_nat (Z : TopCat.{0}) (D : ℕ ⥤ Z.Sheaf AddCommGrpCat.{0})
    [HasColimit D] [HasColimit (D ⋙ underlyingSheaf Z)] :
    IsIso (colimit.post D (underlyingSheaf Z)) :=
  canonicalComparison_isIso Z D

/-- Filtered colimit preservation includes the empty topological space. -/
private theorem preserves_empty :
    PreservesColimitsOfShape ℕ (underlyingSheaf (TopCat.of PEmpty.{1})) :=
  preservesFilteredColimits (TopCat.of PEmpty.{1})

/-- The native stage-leg equation is valid over the empty space. -/
private theorem stage_empty (D : ℕ ⥤ (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0})
    [HasColimit D] [HasColimit (D ⋙ underlyingSheaf (TopCat.of PEmpty))] (stage : ℕ) :
    colimit.ι (D ⋙ underlyingSheaf (TopCat.of PEmpty)) stage ≫
      colimit.post D (underlyingSheaf (TopCat.of PEmpty)) =
        (underlyingSheaf (TopCat.of PEmpty)).map (colimit.ι D stage) :=
  canonicalComparison_stage (TopCat.of PEmpty) D stage

/-- The literal native comparison is invertible over the empty space. -/
private theorem iso_empty (D : ℕ ⥤ (TopCat.of PEmpty).Sheaf AddCommGrpCat.{0})
    [HasColimit D] [HasColimit (D ⋙ underlyingSheaf (TopCat.of PEmpty))] :
    IsIso (colimit.post D (underlyingSheaf (TopCat.of PEmpty))) :=
  canonicalComparison_isIso (TopCat.of PEmpty) D


end SheafCohomologyExamples.AbelianForgetFilteredColimitsClient

/-! Private compact-open and derived-colimit clients of the aggregate API. -/

section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SheafCohomologyExamples

private theorem compactOpenColimitComparison
    {X : TopCat.{0}} [PrespectralSpace X] [QuasiSeparatedSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {I : Type} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0})
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsIso (colimit.post F (SheafCohomology.CompactOpenSections.sections U)) :=
  SheafCohomology.CompactOpenSections.canonicalSectionsComparison_isIso F U hU

private theorem degreeZeroFilteredColimit
    {X : TopCat.{0}} [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasExt.{0} (X.Sheaf AddCommGrpCat.{0})]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {I : Type} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0}) :
    PreservesColimit F
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0) :=
  SheafCohomology.DegreeZero.preservesColimit_functorH_zero F

private theorem allDegreeDerivedColimit
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
    [HasExt.{0} (X.Sheaf AddCommGrpCat.{0})]
    {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0}) (hf : IsSpectralMap f) (q : ℕ) :
    IsIso (colimit.post F
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q)) :=
  SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_isIso
    f F hf q

private theorem allDegreeDerivedColimitStage
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
    {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0}) (q : ℕ) (i : I) :
    colimit.ι
        (F ⋙ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) i ≫
      colimit.post F
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) =
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q).map
      (colimit.ι F i) :=
  SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_ι
    f F q i

end SheafCohomologyExamples

end
