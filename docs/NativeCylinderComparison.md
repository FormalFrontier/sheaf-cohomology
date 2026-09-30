<!-- SPDX-License-Identifier: Apache-2.0 -->
# Chosen native cylinder limits and original-stage sections

Import `SheafCohomology.NativeCylinderComparison` directly, or use the aggregate
`SheafCohomology` root, which re-exports this module since the 79-module release. This is a
reusable comparison for actual native limits, not an alternative diagram or a
spectral invertibility theorem.

## Data and chosen native comparison

Fix `ι : Type v` with `[Preorder ι] [IsDirectedOrder ι]`, an explicit
`i0 : ι`, a diagram
`N : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} (Type v)`, and an
*actual* cone `m : Cone N` with `hm : IsLimit m`. Choose any
`U0 : Opens (N.obj (op i0))`; it may be empty. The principal tail
`Set.Ici i0` is inhabited by `i0` and filtered by the directed preorder,
without a linear-order or nonempty-open hypothesis. The inherited
`restricted N i0 U0` uses the actual native open restrictions, and
`restrictedCone N i0 m U0` has the literal restriction of `m.pt` as its
vertex.

`restrictedSpaceIsLimit N i0 m hm U0` applies the published
`SheafedSpace.preservesLimitForgetOfHasLimit` to the inherited *native*
`restrictedIsLimit`. It supplies the forgotten-space limit needed by the
published `SheafedSpace.limitConeOfSpaceCone`; it is not a general assertion
that forgetting an arbitrary native limit preserves it. Write `Q` for this
chosen native limit and `R` for `restrictedCone N i0 m U0`. Then
`chosenLimitIso N i0 m hm U0 : Q.cone.pt ≅ R.pt` compares the chosen
construction with the literal restriction. The theorems
`chosenLimitIso_hom_projection` and `chosenLimitIso_inv_projection` give
both native projection equations, not just equations of underlying spaces.
`chosenLimitIso_hom_base` and `chosenLimitIso_inv_base` additionally state
that both underlying base maps are the identity on the literal cylinder
space, by the forgotten limiting cone's hom-extensionality.

## Contravariant sections and exact stage law

`restrictedGlobalSectionsComparison N i0 m hm U0` maps the colimit of
the *actual restricted-stage* global sections to
`m.pt.presheaf.obj (op (coneOpen N i0 m U0))`. It composes
`SheafedSpace.nativeGlobalSectionsComparison` for `Q`,
`SheafedSpace.Γ.map (chosenLimitIso N i0 m hm U0).inv.op`, and the
`eqToHom` from `SheafedSpace.restrict_Γ_obj` for `R.pt`.
The **inverse** is needed because `Γ` reverses native arrows; no desired
`IsIso` premise is introduced.

`colimit_ι_restrictedGlobalSectionsComparison` identifies each colimit
leg with `Γ.map` of the actual restricted-cone projection followed by
the restriction-object `eqToHom`. More precisely,
`originalStage_restrictedGlobalSectionsComparison` precomposes that leg
with the *inverse* stage restriction-object cast
`eqToHom (SheafedSpace.restrict_Γ_obj (N.obj (op i.1))
  (stageOpen N i0 U0 i)).symm`. Its right-hand side is the actual
original native projection's presheaf component
`(m.π.app (op i.1)).hom.c.app (op (stageOpen N i0 U0 i))`, followed by
`eqToHom` of the inverse-image-open equality
`(coneOpen_eq_stage N i0 m U0 i).symm` after applying
`fun W : Opens m.pt => m.pt.presheaf.obj (op W)`. These casts are explicit;
the original stage is not silently identified with its native restriction.

`SheafCohomologyExamples.NativeCylinderComparison` uses an ordinary
`import SheafCohomology.NativeCylinderComparison`. Its private theorem
`chosen_projection_and_original_stage` simultaneously uses the inverse
native projection law, both base identities and the exact original-stage
section equation for arbitrary `U0`, including the empty case. It does
not posit a restricted limit or a section law as a hypothesis.
