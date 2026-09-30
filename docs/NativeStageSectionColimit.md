<!-- SPDX-License-Identifier: Apache-2.0 -->
# Native stage sections and the cone-pullback colimit

`SheafCohomology.NativeStageSectionColimit` publicly exports the **named theorem**
`AlgebraicGeometry.SheafedSpace.isIso_colimMap_coneSections`. Let
`J : Type v` have `[SmallCategory J]` and `[IsFiltered J]`, and let
`N : Jᵒᵖ ⥤ SheafedSpace (Type v)`. For a cone `c` over the *actual*
underlying-space diagram `N ⋙ SheafedSpace.forget (Type v)` with
`hc : IsLimit c`, assume spectral underlying stage spaces and spectral
underlying transition maps. Then

```lean
IsIso (colimMap (SheafCohomology.ConePullbackSections.coneSections N c))
```

compares the literal same-universe Type-valued stage functors
`N.rightOp ⋙ SheafedSpace.Γ` and
`SheafedSpace.conePullback (Type v) N c ⋙
SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)`.
It does not require inhabited stages, a preorder, injective or surjective
stage transitions, or an assumption that the desired map is an isomorphism.
The theorem is not installed as a global `IsIso` instance.

The injectivity proof obtains a common source-stage representative of two
colimit elements; filtered equality of their target-stage images yields a
later equality of projection units. The native stage-section equality result
then supplies one more arrow witnessing equality in the source colimit.
For surjectivity, a target-colimit representative lifts at a later stage by
`exists_native_stage_section_lift`; the actual cone-section stage leg and
colimit cocone law compute its image. `isIso_iff_bijective` packages the
isomorphism of this exact `colimMap`.

`SheafCohomologyExamples.NativeStageSectionColimit` uses an **ordinary**
`import SheafCohomology.NativeStageSectionColimit`. Its two declarations
remain **private**, not exported public theorems: one cancels the actual
`colimMap` to recover equality of source-colimit elements; the other
recovers a target coprojection from `inv (colimMap η)` after installing the
theorem's `IsIso` witness *locally*. Neither client assumes injectivity,
surjectivity, a comparison isomorphism, or a lifting premise.

For the pinned dependency graph, cache-first build and full
verification boundaries, see the [project README](../README.md#build-and-verification).
