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

The exact inherited toolchain is Lean `v4.34.0-rc2`, with mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official Spectral14
`452b7b7be1bea76434cd083b1019a26f96b4ab30` and inherited official
Ideal `001e3b7508184ecd51e0d86177cb1d54508bf59d`. The destination
depends on local sheaf modules, not on an incubator or source checkout.
From this repository root, fetch the matching cache **before** a focused
build with the pinned toolchain:

```sh
lake exe cache get
lake build SheafCohomology.NativeStageSectionColimit SheafCohomologyExamples.NativeStageSectionColimit
```

## Provenance and status

The **full original producer and client proof expressions are copied and
mechanically transferred**, not merely inspired by an argument. Originals:
FormalFrontier/incubator commit
`1bad295cf6a96a5da13105442982a55e17efb5ec` (tree
`03b2028da5e4e03d324adf6c683d97a4d82831a0`), producer blob
`f8966a17216572a0316604118c37e41d7348070d` and client blob
`770f312d7b9f5f1cf949fd60d9442399abdc76d8`. Reversing only the
producer's one import and the client's one ordinary import plus its
namespace/end substitutions recovers those exact blobs. The original
implementation and complete proof expressions are by worker-b Hive Task
`hive-request-bf36c0a2309835a3fdfa6d14f20ebde4191ab672`
(UID `1addeab3-992e-4fed-aa4b-afcea8e2487c`); its separate unchanged-input
evidence is commit `0568c4e2f088f6b44727883bf564b095bf9c54b0`.
Fresh independent review is by worker-a Hive Task
`hive-request-7b1e8ba3ec50fa7889d32b48e6e638db24c101b8`
(UID `a86d4770-966b-43ad-8b5d-ca56f8e44a82`) at commit
`35292e96298179d531f70abfc23d6d85ca17e9fc`,
`reviews/native-stage-section-colimit/REVIEW.md`; Anchor accepted the
original *unregistered* leaf at incubator issue #4/comment 53357.

The existing native equality result is by worker-b Task
`hive-request-83333dedd640d855f159f1c115a70d659ba2c7dc`
(UID `ce8bbfcb-4d1f-4e5f-b043-5ec831bc6bcd`), and whole-stage lifting
by worker-b Task `hive-request-e5e544a630e9b84215130384682791cdebd0aea0`
(UID `3bb51737-f69e-4698-9538-9f0336c572d9`). The official
cone-section transport, native-cone and compact-open prerequisites, and
mathlib filtered-colimit results are **invoked**, not copied from external
source text. Anchor's separate finite-descent design is incubator commit
`4c52c039a83ad2579e4978686c5bc2aac818992e`. Original SPDX and
author headers remain intact. The narrow destination adapter and this
guide are by worker-a Hive Task
`hive-request-0379bab87d7c2b4512b09a37865419d3586e95c2`
(UID `7d5fd314-be18-4a43-8f5c-f6407812944d`).

The original three-file adapter started on then-frozen **unaccepted** Sheaf69
`7c0510d5c17de07b78b0bedce5f9b9783a72027e`, tree
`f8f4f935746b6d636c688fa3e31175d3d9edf086`. After complete adapter intake,
Anchor assembled the original source-only coherent ten-path registration at
2026-09-27 16:39:24 UTC: the three new
payloads and seven existing root/docs/credit/metadata paths. Both new Lean
blobs, all 67 older nonroot Lean files, eleven package objects, toolchain and
CI remain unchanged. The roots now import the producer and private client,
so those roots ARE changed computational inputs. Focused destination evidence
`06e9dbab113c651b06de411a991f09c531aba6ab` covers the three new origins,
not the complete registered 71-module graph.

At that snapshot, Sheaf71 had not received combined-graph acceptance.
Sheaf69 subsequently passed CI538 at 17:03:22 UTC and, after complete owner
evidence intake and its separate acceptance and integration decisions, was
verified on official GitHub as `062370b8657c0691a02bfd01d43f6095383f4487`
at 17:28:53 UTC. This paragraph preserves that chronology, not live branch status.
Exact destination/release review, complete applicable combined checks, owner
acceptance, integration and verified publication are distinct revision-specific
requirements for Sheaf71. Original expression credit and predecessor evidence
are not combined-root approval; changed prerequisite APIs require reassessment.
No chosen native-limit `Γ` comparison, source-specific endpoint or source
coverage is asserted by this contribution.
