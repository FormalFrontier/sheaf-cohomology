/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributor: Hive Task hive-request-c57c813632815e9d350373cdfa7741657fb4852a
UID: 2717d143-2755-441e-83fb-8f9190fbe8f1
Adapted from published SheafCohomology.AbelianForget.Basic by Anchor (source maintainer).
-/
module
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Functors

public section

set_option warningAsError true

/-!
# Underlying sheaves of commutative rings

The native sheaf-composition construction forgets the ring structure without
changing the underlying sheaf of types.

Contributor: Hive Task `hive-request-c57c813632815e9d350373cdfa7741657fb4852a`
(UID `2717d143-2755-441e-83fb-8f9190fbe8f1`). The expression adapts the
published additive construction in SheafCohomology.AbelianForget.Basic at
`e4c7d681e0913fc1dde266cfcfc37763f1d47785` (Anchor, source maintainer).
The underlying sheaf-composition and forgetful functors are mathlib APIs.
-/

universe v

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf.CommRingForget

/-- Forget ring structure in a sheaf of commutative rings on `Z`. -/
@[expose] noncomputable def underlyingSheaf (Z : TopCat.{v}) :
    Z.Sheaf CommRingCat.{v} ⥤ Z.Sheaf (Type v) :=
  sheafCompose (Opens.grothendieckTopology Z) (CategoryTheory.forget CommRingCat.{v})

end TopCat.Sheaf.CommRingForget
