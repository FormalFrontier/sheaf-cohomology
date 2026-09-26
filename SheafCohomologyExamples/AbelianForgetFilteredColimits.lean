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

/-- Native sheafification also provides the Type-valued colimit. -/
private theorem native_underlying_colimit (Z : TopCat.{0})
    (D : ℕ ⥤ Z.Sheaf AddCommGrpCat.{0}) :
    HasColimit (D ⋙ underlyingSheaf Z) :=
  (CategoryTheory.Sheaf.instHasColimitsOfShape (J := Opens.grothendieckTopology Z)
    (D := Type 0) (K := ℕ)).has_colimit _

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
