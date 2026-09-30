<!-- SPDX-License-Identifier: Apache-2.0 -->

# Native lifting of sections to a filtered stage

Import `SheafCohomology.NativeStageSectionLifting`. Let `J : Type v` be a
small filtered category, `N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace (Type v)` a
diagram whose underlying spaces are spectral and whose underlying transition
maps are spectral, and let `c` be a limiting cone over its underlying
topological diagram. The theorem
`AlgebraicGeometry.SheafedSpace.exists_native_stage_section_lift` accepts a
stage `i : J` and an element `s` of the **actual** cone-pullback sheaf's global
sections at `i`. It produces `j : J`, `g : i ⟶ j`, and a native global section
`a : (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj j` satisfying the
literal equation

```lean
(SheafCohomology.ConePullbackSections.coneSections N c).app j a =
  (AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
    SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s
```

The hypotheses are a small filtered index category, a limiting cone for the
underlying spaces, spectral stage spaces, and spectral transition maps. No
stage-inhabitedness, nonempty cover, preorder, transition injectivity or
endpoint-isomorphism hypothesis is required. In particular, the empty-indexed
finite cover and empty-stage cases use the existing sheaf condition and do not
choose a point. This proves an element-level later-stage lift, **not** a
filtered-colimit comparison, endpoint isomorphism, or source-coverage claim.

The proof represents the cone-pullback section on a finite compact-open
cover, descends that cover to one whole native stage, transports the actual
projection-unit equalities through the restricted adjoint triangle, synchronizes
finite overlap equalities on a coherent filtered wide span, glues native local
sections, and recovers the given pullback section by sheaf separatedness. The
finite synchronization, transport, and gluing lemmas are private; the lifting
theorem is public. This is the existing native `SheafedSpace.Γ` functor and the
existing cone-section transformation, not a replacement stage functor.

For ordinary clients, `import SheafCohomology.NativeStageSectionLifting` suffices.
`SheafCohomologyExamples.NativeStageSectionLifting` uses an **ordinary** import
and has two **private** declarations: a later native section exists, and the
chosen lift remains valid after every further native arrow by naturality.
They are example clients, not additional public APIs. The producer's `public
import` declarations describe its imported modules, not the visibility of these
private client declarations. The producer additionally imports
`SheafCohomology.NativeStageSectionEquality`,
`SheafCohomology.ConePullbackSections`,
`SpectralStoneDuality.FiniteCylinderDescent`, and
`SpectralStoneDuality.Limits` as public imports.

For the pinned dependency graph, cache-first build and full
verification boundaries, see the [project README](../README.md#build-and-verification).
