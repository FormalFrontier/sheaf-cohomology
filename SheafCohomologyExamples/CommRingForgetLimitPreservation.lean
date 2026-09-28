/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Hive Task hive-request-c57c813632815e9d350373cdfa7741657fb4852a
UID: 2717d143-2755-441e-83fb-8f9190fbe8f1
-/
module
public import SheafCohomology.CommRingForget.LimitPreservation

public section

/-!
# Universal property of the forgotten native cone

The original projection maps, not projections transported from a replacement
cone, characterize the forgetful image of every limiting commutative-ring cone.

Contributor: Hive Task `hive-request-c57c813632815e9d350373cdfa7741657fb4852a`
(UID `2717d143-2755-441e-83fb-8f9190fbe8f1`).
-/

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v

namespace SheafCohomologyExamples.CommRingForgetLimitPreservation

/-- The original forgotten projections give the unique mediating morphism
from any Type-valued sheafed-space cone over the actual forgotten diagram. -/
theorem uniqueLift {J : Type v} [SmallCategory J] [IsFiltered J]
    (S : Jᵒᵖ ⥤ SheafedSpace CommRingCat.{v}) (m : Cone S) (hm : IsLimit m)
    (c : Cone (S ⋙ SheafedSpace.CommRingForget.underlying)) :
    ∃! f : c.pt ⟶ SheafedSpace.CommRingForget.underlying.obj m.pt,
      ∀ i : Jᵒᵖ,
        f ≫ SheafedSpace.CommRingForget.underlying.map (m.π.app i) = c.π.app i := by
  have hPreservation : PreservesLimit S SheafedSpace.CommRingForget.underlying :=
    SheafedSpace.CommRingForget.preservesCofilteredLimit S
  have hc : IsLimit (SheafedSpace.CommRingForget.underlying.mapCone m) :=
    (hPreservation.preserves hm).some
  refine ⟨hc.lift c, ?_, ?_⟩
  · intro i
    exact hc.fac c i
  · intro f hf
    apply hc.hom_ext
    intro i
    rw [hc.fac c i]
    exact hf i

end SheafCohomologyExamples.CommRingForgetLimitPreservation
