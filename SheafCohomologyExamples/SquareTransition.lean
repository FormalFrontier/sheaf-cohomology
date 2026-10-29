/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SheafCohomology.SquareTransition
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
deprecated_module (since := "2026-10-27")

public section

set_option warningAsError true

/-!
# Deprecated compatibility import

Import `SheafCohomology.SquareTransition` for the canonical square-transition API.
This legacy path is a public-import compatibility shim with its original imports
retained. Actual public availability is not yet established; retain this path for
at least three calendar months after that eventual availability.
-/
