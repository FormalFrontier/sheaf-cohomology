# sheaf-cohomology

This 103-module library develops sheaf cohomology, compact-open sections, and
native limits and sections of sheafed spaces, including original-open
commutative-ring cylinders and the open-variable naturality of their generic,
ring and additive section comparisons. It also compares the actual native
section diagrams when their principal tail changes by transition pullback.
Import [`SheafCohomology`](SheafCohomology.lean) for the aggregate API or an
individual subject module for a smaller import. These results are declarations
of this library, built on mathlib and its published dependencies; they are not
a claim to have formalized an entire source. The
[open-naturality guide](docs/NativeCylinderOpenNaturality.md) describes the new
generic restriction and comparison arrows and their precise hypotheses; the
[tail-change guide](docs/NativeCylinderTailChange.md) describes the later-stage
diagram and colimit comparison.

## Headline results

- **Compact-open sections and acyclicity.** On a prespectral,
  quasi-separated space, evaluation of suitable concrete-category sheaves on
  a compact open preserves small filtered colimits, subject to the explicit
  sheafification, concrete-category and universe assumptions. For abelian
  sheaves on a *compact* such space, quasi-flasqueness implies vanishing of
  positive-degree sheaf cohomology, using an injective-envelope dimension
  shift. See
  [`preservesColimit_sections`](SheafCohomology/CompactOpenSections.lean#L784),
  [`subsingleton_H_succ`](SheafCohomology/QuasiFlasqueAcyclicity.lean#L259),
  and the [mathematical guide](docs/Guide.md).
- **Higher direct images.** For a spectral map from a prespectral,
  quasi-separated source to a prespectral target, right-derived pushforward
  of abelian sheaves preserves filtered colimits in every natural degree. The
  theorem identifies the *canonical* `colimit.post` comparison for a small,
  nonempty directed-preorder diagram, not an arbitrary isomorphism; this API
  has universe-zero spaces, coefficients and Ext groups and requires its
  stated sheafification/Ext instances. See
  [`rightDerivedPushforward_colimitPost_isIso`](SheafCohomology/HigherDirectImageFilteredColimit.lean#L332)
  and the [mathematical guide](docs/Guide.md).
- **Native sheafed-space limits.** For an actual cone, a limiting underlying
  space cone and a colimiting cocone of its projection-pullback sheaves imply
  that the native cone is limiting; over that same limiting base, the converse
  recovers the sheaf colimit. A separate construction builds such a native
  limit when the required coefficient colimits and local weak sheafification
  exist. These are conditional results under the concrete-coefficient
  hypotheses, not a global limits instance. See the
  [limit criterion](SheafCohomology/ConePullbackLimit.lean#L222),
  [fixed-base converse](SheafCohomology/ConePullbackLimitConverse.lean#L170),
  [construction](SheafCohomology/LimitConstruction.lean#L62), and
  [limit guide](docs/ConePullbackLimit.md).
- **Forgetting coefficients.** The native additive-to-Type and
  commutative-ring-to-Type functors preserve same-universe cofiltered limits
  of sheafed spaces, using canonical pullback mates and filtered sheaf-colimit
  comparisons. The ring pullback `canonicalComparison` is a *different* map
  from the filtered-diagram `colimit.post` comparison; neither preservation
  theorem covers arbitrary diagram shapes. See the
  [additive theorem](SheafCohomology/AbelianForget/LimitPreservation.lean#L103),
  [ring theorem](SheafCohomology/CommRingForget/LimitPreservation.lean#L112),
  and [ring guide](docs/CommRingForget.md).
- **Global sections of spectral inverse limits.** Filtered colimits of
  native stage sections recover the global sections of the constructed
  Type-valued native limit, and of the *original actual limiting cone* for
  additive or commutative-ring coefficients. All three isomorphisms require
  small filtered indexing, spectral original stages and spectral original
  transition maps. In the ring case each limit section comes from
  *some* stage, not from every fixed stage. See the
  [Type comparison](SheafCohomology/NativeLimitGlobalSections.lean#L181),
  [additive comparison](SheafCohomology/NativeAdditiveGlobalSections.lean#L99),
  [ring comparison and stage theorem](SheafCohomology/NativeCommRingGlobalSections.lean#L105),
  and [ring sections guide](docs/NativeCommRingGlobalSections.md).
- **Compact-open cylinders.** For a directed preorder and a selected index,
  restricting an actual native limit to the inverse image of a compact stage
  open gives filtered-colimit descriptions of sections over that open for
  Type-valued, additive and commutative-ring sheafed spaces. For an arbitrary
  original cone, the actual restricted-stage section diagrams also vary
  contravariantly with the stage open: their colimits form a presheaf under
  the stated family of `HasColimit` assumptions, and the comparison to the
  original cone commutes with open restriction. Ring and additive restriction
  squares identify their existing arrows with this generic comparison; none
  of these arrow laws asserts an all-open isomorphism. The
  change-of-principal-tail result uses the actual transition-pullback open:
  the later native and section diagrams are isomorphic to the earlier diagrams
  restricted along the final tail inclusion. Colimit existence transfers both
  ways; one local `HasColimit` at the earlier tail yields the canonical iso,
  coprojection law and an arbitrary-original-cone comparison square with a
  forward target equality cast. This makes no all-open `IsIso` or identity/
  composition claim for tail changes. Separately, the conditional ring result
  compares the literal restricted tail-stage rings with sections
  on the *original* cone's inverse-image open: its original-stage law uses the
  actual projection and both equality transports in `CommRingCat`. For an actual
  limiting cone, spectral original stages and transition maps, and a compact
  possibly-empty stage open, this comparison is an isomorphism, and each
  section comes from *some* tail stage, not every fixed stage. No nonempty-open,
  nontrivial-ring or transition-surjectivity premise is needed. See the
  [Type theorem](SheafCohomology/NativeSpectralCylinderSections.lean#L45),
  [additive theorem](SheafCohomology/NativeAdditiveCylinderSections.lean#L101),
  [ring IsIso and some-stage declarations](SheafCohomology/NativeCommRingCylinderSections.lean),
  [additive cylinder guide](docs/NativeAdditiveCylinderSections.md),
  [generic open-naturality guide](docs/NativeCylinderOpenNaturality.md),
  [generic tail-change guide](docs/NativeCylinderTailChange.md),
  [`betweenTailInclusion_final`](SheafCohomology/NativeCylinderTailChange.lean),
  [`cylinderSectionsTailColimitIso`](SheafCohomology/NativeCylinderTailChange.lean),
  [`cylinderSectionsComparison_betweenTail`](SheafCohomology/NativeCylinderTailChange.lean), and
  [ring-cylinder guide](docs/NativeCommRingCylinderSections.md).

## Scope and navigation

The [mathematical guide](docs/Guide.md) maps modules, proofs, examples and
limitations. Focused guides cover [native cones and limits](docs/ConePullbackLimit.md),
[the constructed native limit](docs/SheafedSpaceLimitConstruction.md),
[additive](docs/AbelianSheafedSpaceCofilteredLimits.md) and
[ring](docs/CommRingForget.md) coefficient forgetting,
[global-section comparisons](docs/NativeLimitGlobalSections.md),
[compact-open additive cylinders](docs/NativeAdditiveCylinderSections.md),
[ring cylinders](docs/NativeCommRingCylinderSections.md),
[open-variable naturality](docs/NativeCylinderOpenNaturality.md) and
[principal-tail changes](docs/NativeCylinderTailChange.md).

Some constructions start with an *actual* cone or cocone; a theorem that
recognizes a limit does not supply limits for arbitrary shapes or coefficients.
The separate native limit constructor requires the stated coefficient colimits
and weak sheafification. Generic cylinder comparisons and open restriction
squares work for arbitrary original cones; invertibility and some-stage
representation require their additional spectral, compactness and original-limit
hypotheses. The Type-valued and additive/ring results have distinct concrete
coefficient and universe constraints. In particular, the all-degree filtered
right-derived theorem is at universe zero; the sheafified local-cohomology
comparison used in its proof has its own positive-degree scope.

The [native API reference](docs/API.md) and its
[manifest](docs/api-manifest.json) describe only a frozen historical 26-module
input: 556 display sites (545 top-level plus 11 nested), with 399 source
docstrings, 157 generic pointers and 12 source-local instance annotations.
They are not a current 103-module or private-axiom inventory; the
[documentation contract](docs/README.md) explains their exact frozen scope.
Focused guides and the Lean declarations themselves supply the remaining
signatures. Examples under
[`SheafCohomologyExamples`](SheafCohomologyExamples.lean) demonstrate ordinary
imports; many example declarations are intentionally private.

## Build and verification

Use the repository-pinned `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, and official
`spectral-stone-duality` commit
`452b7b7be1bea76434cd083b1019a26f96b4ab30` (bringing official
`ideal-completion` at `001e3b7508184ecd51e0d86177cb1d54508bf59d`).
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` bind the complete
resolved inputs. Access to the published dependencies currently requires
authorized access to their private GitHub repositories; importing this
library does not require a source-research or incubator checkout.

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake --wfail build
```

Run these from the repository root; the matching precompiled mathlib cache
must be fetched successfully *before* the build. The default targets contain
both the library and ordinary-import examples. For release acceptance,
a successful applicable build and a complete transitive axiom audit of all
repository declarations, including generated and private declarations and
examples, are required. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. A source grep, a selected public-declaration sample or a separate
stored-proof replay is not a substitute for those checks. Reuse existing
applicable evidence when checking inputs have not changed; this prose
contribution makes no new build, axiom-audit or performance claim.

Historical resource observations are scoped to *different*, older workloads:
for the 26-module documentation baseline in a four-CPU, 15 GiB cgroup, the
author reported 1m24s for cache fetch, 16m26s for a 2,373-job default
build and 1m13s for the doc-generator build. The native documentation batch
spanned 2m28s in retained start/end timestamps; the other three reported
durations lack separate timestamped command ledgers. The cgroup's peak
included filesystem cache, and 1,735 `memory.events max` events were *not*
OOM or kill events. A later expanded workload took about 9m02s for 2,378
jobs in another cache state. The recorded `LAKE_JOBS=2` setting is not
an effective Lake scheduling control; `LEAN_NUM_THREADS` is not a global
memory bound. None of these historical observations establishes a measured
minimum or limit for this 103-module tree. See the precise frozen
[documentation and cost record](docs/README.md).

## References and credits

The mathematical background includes Kazuhiro Fujiwara and Fumiharu Kato,
*Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5), alongside Lean,
mathlib and the declared formal dependencies. Formal Frontier AI agents
wrote and independently reviewed the original development, with Anchor
coordinating and other credited contributors and reviewers documented in
[credits](docs/CREDITS.md) and repository history. Andrew Yang's Apache-2.0
mathlib open-immersion work is reused and credited there. Collective author
credit does not assert copyright ownership, third-party relicensing, source
author endorsement, human review or complete formal coverage of a source.
For original project material, the header credit is literally
`Authors: Formal Frontier Agents` with
`SPDX-License-Identifier: Apache-2.0`; the full
[Apache-2.0 license](LICENSE) accompanies this library. These are authorship
and license statements, not a claim of copyright ownership or a license to
relabel authentic upstream material.
`formalization.yaml` records concise candidate-specific public metadata;
exact release acceptance and publication evidence remain separate.
