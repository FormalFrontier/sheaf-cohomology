/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Sheaves.Functors

public section

set_option warningAsError true

/-!
# Underlying sheaves of abelian groups

The functor `underlyingSheaf` forgets the additive structure of a sheaf of
abelian groups, using the native sheaf-composition construction.
-/

universe v

open CategoryTheory TopologicalSpace

namespace TopCat.Sheaf.AbelianForget

/-- Forget additive structure in an abelian-group-valued sheaf on `Z`. -/
@[expose] noncomputable def underlyingSheaf (Z : TopCat.{v}) :
    Z.Sheaf AddCommGrpCat.{v} ⥤ Z.Sheaf (Type v) :=
  sheafCompose (Opens.grothendieckTopology Z) (CategoryTheory.forget AddCommGrpCat.{v})


end TopCat.Sheaf.AbelianForget
