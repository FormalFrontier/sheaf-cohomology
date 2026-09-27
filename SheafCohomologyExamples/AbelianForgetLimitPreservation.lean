/- SPDX-License-Identifier: Apache-2.0
Original expression author: Worker B, Hive Task hive-request-13fb7168e78b10adc0a739488a5b88a5bad2cd58
UID: 9a8d7368-37db-444c-b740-2b889ce82678. -/

module
public import SheafCohomology.AbelianForget.LimitPreservation

public section

/-!
# Native cofiltered limit preservation clients

Arbitrary additive diagrams and limiting cones exercise the local preservation
witness at both a three-stage index and the infinite directed index `ℕ`.
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v

namespace SheafCohomologyExamples.AbelianForgetLimitPreservation

private def finiteFirst : (0 : Fin 3) ⟶ (1 : Fin 3) := homOfLE (by decide)
private def finiteSecond : (1 : Fin 3) ⟶ (2 : Fin 3) := homOfLE (by decide)

private noncomputable def finitePreserved
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0})
    (C : Cone S) (hC : IsLimit C) :
    IsLimit (SheafedSpace.AbelianForget.underlying.mapCone C) := by
  letI : PreservesLimit S SheafedSpace.AbelianForget.underlying :=
    SheafedSpace.AbelianForget.preservesCofilteredLimit S
  exact isLimitOfPreserves SheafedSpace.AbelianForget.underlying hC

private theorem finiteComposite
    (S : (Fin 3)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0})
    (C : Cone S) (hC : IsLimit C) :
    (SheafedSpace.AbelianForget.underlying.mapCone C).π.app (op (2 : Fin 3)) ≫
        (S ⋙ SheafedSpace.AbelianForget.underlying).map
          (finiteFirst ≫ finiteSecond).op =
      (SheafedSpace.AbelianForget.underlying.mapCone C).π.app (op (0 : Fin 3)) := by
  have _ := finitePreserved S C hC
  exact (SheafedSpace.AbelianForget.underlying.mapCone C).w
    (finiteFirst ≫ finiteSecond).op

private def natFirst : (0 : ℕ) ⟶ (1 : ℕ) := homOfLE (by decide)
private def natSecond : (1 : ℕ) ⟶ (2 : ℕ) := homOfLE (by decide)

private noncomputable def natPreserved
    (S : (ℕ)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0})
    (C : Cone S) (hC : IsLimit C) :
    IsLimit (SheafedSpace.AbelianForget.underlying.mapCone C) := by
  letI : PreservesLimit S SheafedSpace.AbelianForget.underlying :=
    SheafedSpace.AbelianForget.preservesCofilteredLimit S
  exact isLimitOfPreserves SheafedSpace.AbelianForget.underlying hC

private theorem natComposite
    (S : (ℕ)ᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{0})
    (C : Cone S) (hC : IsLimit C) :
    (SheafedSpace.AbelianForget.underlying.mapCone C).π.app (op (2 : ℕ)) ≫
        (S ⋙ SheafedSpace.AbelianForget.underlying).map
          (natFirst ≫ natSecond).op =
      (SheafedSpace.AbelianForget.underlying.mapCone C).π.app (op (0 : ℕ)) := by
  have _ := natPreserved S C hC
  exact (SheafedSpace.AbelianForget.underlying.mapCone C).w
    (natFirst ≫ natSecond).op

private noncomputable def polymorphicPreserved {J : Type v} [SmallCategory J] [IsFiltered J]
    (S : Jᵒᵖ ⥤ SheafedSpace AddCommGrpCat.{v}) (C : Cone S) (hC : IsLimit C) :
    IsLimit (SheafedSpace.AbelianForget.underlying.mapCone C) := by
  letI : PreservesLimit S SheafedSpace.AbelianForget.underlying :=
    SheafedSpace.AbelianForget.preservesCofilteredLimit S
  exact isLimitOfPreserves SheafedSpace.AbelianForget.underlying hC

end SheafCohomologyExamples.AbelianForgetLimitPreservation
