<!-- SPDX-License-Identifier: Apache-2.0 -->
# Global sections of a chosen native sheafed-space limit

`SheafCohomology.NativeLimitGlobalSections` compares the colimit of the
**actual native stage global sections** with global sections of a chosen
native sheafed-space limit. Import this module directly or use the aggregate
`SheafCohomology` public root. It is a reusable mathematical API, not a
source-passage or source-coverage claim.

## Exact data and maps

Fix `J : Type v` with `[SmallCategory J]` and `[IsFiltered J]`, a diagram
`N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} (Type v)`, and an
*actual* underlying-space cone
`c : Cone (N ⋙ SheafedSpace.forget (Type v))` with `hc : IsLimit c`.
The native limit is the existing
`Q := SheafedSpace.limitConeOfSpaceCone (Type v) N c hc`. The statement
uses the same universe `v` for the small filtered index, spaces and
Type-valued sheaves. Write `S := N.rightOp ⋙ SheafedSpace.Γ` only as an
abbreviation, not a replacement diagram.

`AlgebraicGeometry.SheafedSpace.nativeGlobalSectionsCocone N c hc : Cocone S`
has vertex `SheafedSpace.Γ.obj (op Q.cone.pt)` and stage legs exactly

```lean
SheafedSpace.Γ.map (Q.cone.π.app (op i)).op
```

`nativeGlobalSectionsComparison N c hc` is the actual
`colimit.desc _ (nativeGlobalSectionsCocone N c hc)`. Its projection law
`colimit_ι_nativeGlobalSectionsComparison N c hc i` says

```lean
colimit.ι S i ≫ nativeGlobalSectionsComparison N c hc =
  SheafedSpace.Γ.map (Q.cone.π.app (op i)).op
```

The factorization `nativeGlobalSectionsComparison_eq_colimMap_post N c hc`
identifies **this** descended map with

```lean
colimMap (SheafCohomology.ConePullbackSections.coneSections N c) ≫
  colimit.post (SheafedSpace.conePullback (Type v) N c)
    (SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt))
```

Here the proof installs *locally* the same
`CategoryTheory.Sheaf.instHasColimitsOfShape` for `c.pt.Sheaf (Type v)`
used in the native construction. It compares each coprojection via the
published cone-pullback section leg, official
`limitConeOfSpaceCone_π_mate_colimit_ι`, the sheaf adjunction unit and
`sheafMate_adjoint`, then applies `colimit.hom_ext`. The codomain remains
`Γ(Q.cone.pt)`; no alternate native limit or arbitrary colimit-choice
identification is substituted.

For the isomorphism, additionally assume exactly

```lean
hstage : ∀ k : Jᵒᵖ,
  SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k)
htransition : ∀ {k l : Jᵒᵖ} (f : k ⟶ l),
  IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)
```

The named theorem
`isIso_nativeGlobalSectionsComparison N c hc hstage htransition`
proves `IsIso (nativeGlobalSectionsComparison N c hc)`, not a global
instance. It composes the moving-stage
`isIso_colimMap_coneSections` with the fixed-base
`CompactOpenSections.canonicalSectionsComparison_isIso` at the compact
top open. Official `SpectralStoneDuality.Limits` supplies compactness,
prespectrality and quasi-separatedness of the cofiltered spectral-space
limit; `hc.conePointUniqueUpToIso` and `TopCat.homeoOfIso` transfer them
to `c.pt`. No desired-`IsIso`, inhabited-stage, cover or alternate-limit
premise is assumed.

`SheafCohomologyExamples.NativeLimitGlobalSections` uses an **ordinary**
`import SheafCohomology.NativeLimitGlobalSections`. Its theorem
`nativeProjections_detect_coprojection_eq` is a private client declaration:
equality of two actual projection images implies equality of the two
colimit coprojections by the stated projection law and cancellation of
the named isomorphism. Neither `import all` nor a public wrapper is needed
for downstream use.

## Reproduction and provenance

The project pins Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official Spectral14
`452b7b7be1bea76434cd083b1019a26f96b4ab30`, and the inherited
official Ideal `001e3b7508184ecd51e0d86177cb1d54508bf59d`.
The module depends on local sheaf prerequisites; this deliverable does
**not** depend on an incubator revision. From the project root, after
fetching the pinned toolchain, use the matching mathlib cache before
building the focused modules:

```sh
lake exe cache get
lake build SheafCohomology.NativeLimitGlobalSections SheafCohomologyExamples.NativeLimitGlobalSections
```

Both full Lean statement **and proof expressions** are copied and narrowly
transferred, not merely inspired by the original arguments. The originals
are FormalFrontier/incubator commit
`00d551efc598b8252fbc694830523b830bf94a27` (tree
`00de4a6974fef3683911807b5928f928e7a9030b`): producer blob
`89e1bdca0160dc88665cc6a024bdb24422bebcbc`, client blob
`c4c386299561a77415f1825e55c51e0c38fe86c5`. At the original transfer,
reversing the producer's single public-import substitution and the client's
ordinary import plus two namespace/end substitutions recovered those blobs.
At the original transfer the Apache-2.0 SPDX and worker-author headers stayed
in both files. This unaccepted 85 successor retains both SPDX notices and
complete original worker credit, but reversibly relabels `Authors:` as
collective project credit with `Contributor:` for the workers; reversing the
labels restores the complete pre-repair destination blobs, not the incubator
originals without the earlier import/namespace reversal. Neither current
whole file is identical to the original transfer blob. All bytes
from `module` onward, including the proof expressions, remain unchanged.
The original implementation and complete proof expressions are by
worker-b Hive Task `hive-request-4c216dbec01d4be3c9179c965656f0054d638fb8`
(UID `b5bc6fa6-d9ab-4cfa-bd79-3ec1cdf7265a`). Its complete focused
build and 16-origin standard-axiom evidence is commit
`cad6a92baed502c134939e6dabc7db6135dc1f6d`,
`evidence/native-limit-global-sections/` in the incubator. Eleven
earlier development nonpasses remain historical, not suppressed.

The two compact/prespectral transfer helper proof expressions adapt
worker-b Task `hive-request-e5e544a630e9b84215130384682791cdebd0aea0`
(UID `3bb51737-f69e-4698-9538-9f0336c572d9`)'s native-stage lifting
implementation; the quasi-separated helper follows that topology-transfer
pattern with a different official result. The original collector adapts
the predecessor harness from worker-b Task
`hive-request-bf36c0a2309835a3fdfa6d14f20ebde4191ab672`
(UID `1addeab3-992e-4fed-aa4b-afcea8e2487c`), evidence
`0568c4e2f088f6b44727883bf564b095bf9c54b0`. Anchor's separate
*design*, not a compiled proof, is incubator commit
`4c52c039a83ad2579e4978686c5bc2aac818992e`. Other cited published
mathematics is invoked, not copied. This narrow adapter and guide are by
worker-a Hive Task `hive-request-4a0c71a3b9ce2bd856ab1a6b47ce89a98433112e`
(UID `eb69c4df-f917-40c5-b2c6-b5b1c344080f`).

The original was accepted as an **unregistered** incubator leaf by Anchor
at incubator issue #4/comment 53518 after full intake #4/comment 53474,
following author-distinct worker-a review
`5de42c13795f2b53f09f3aaf3955a74832ebfa06`,
`reviews/native-limit-global-sections/REVIEW.md`, by Task
`hive-request-63bb28dd0ebca9eed6f1f8633171e93fdbe4cf95`
(UID `ef75b120-2781-4310-bec4-25989baec649`). Its **one guide
correction** replaces the original handoff's mistaken predecessor citation
#4/comment 53341 with Anchor's #4/comment 53357; the original author
README/handoff remains a historical record. The moving-stage input
`1bad295cf6a96a5da13105442982a55e17efb5ec` is accepted but
unregistered; source-root registration and release are not implied.

At the 2026-09-27 17:05 UTC registration snapshot, the transfer started at frozen
**unaccepted** Sheaf71
`7aa59f0e087045625022cc448d14fa96458725ab` (tree
`898d253d20fac474c75e82dbc03a79ad12dc38c5`). Anchor recorded
source-only registration at sheaf-cohomology issue #34/comment 53517,
not final code approval. Its parent Sheaf69 `7c0510d` then had pending owner
CI evidence intake, main, prep and publication gates; CI538 itself had already
succeeded at 17:03:22 UTC. The earlier Sheaf67 release did not
approve this successor. Anchor consumed the complete adapter and separate
evidence at sheaf-cohomology issue #34/comment 53591, and registered these
unchanged Lean payloads in the source-only 73-module aggregate with navigation,
metadata and credit. The original adapter is
`68d837027efcd3e61dd5ef80ff9a0153f8e178e0`; its separate focused evidence is
`0ce32352e38c75721ee011e132ea513d4c589a69`, with fifteen producer origins and
one private-client origin, including four private-prefix origins, all
standard-three. The new root imports ARE changed computational inputs, not
covered by that focused evidence. At that snapshot, this coherent registration
had **not** been independently reviewed, accepted, integrated or released in the destination.
Fresh destination/release review, full applicable combined CI, owner acceptance
and verified publication are separate revision-specific decisions, as are both
predecessor decisions. Subsequently, full owner intake of the successful CI538
artifact and the separate Sheaf69 owner main/prep/public gates completed; official GitHub commit
`062370b8657c0691a02bfd01d43f6095383f4487` was verified on 2026-09-27
at 17:28:53 UTC. This later predecessor release does not approve Sheaf71 or this
73-module registration. These dated records are not a live release-status feed.

The corrected Sheaf71 documentation snapshot
`64efb52e27eba493fcf2f13123bb75cbe4929b87` subsequently passed full CI566
at 2026-09-27 19:18:10 UTC. After complete owner evidence intake and separate
main, internal and public decisions and protected integration, its official
GitHub release `75d708bf56eeec2de6c599b16cb96c82c961c9fe` was verified at
19:26:30 UTC. The 73-module successor merged that accepted ancestry
without rewriting the original `e570bfbb0a56dd38c43e9ed1c10057205e6088aa`
candidate or changing any of its 73 Lean blobs, roots, eleven pins or CI inputs.
It also carries the accepted predecessor's corrected stage-colimit guide.
Original73 CI558 had succeeded at 18:52:33 UTC; its fully intaken both-target
and private-inclusive standard-axiom evidence applied only to unchanged
computational inputs, not as a fresh execution on the documentation successor.
Its later final independent review, applicable checks, owner decisions and
protected integration supported official 73 release
`6aa8528f28264d9b44de0f31e72696d8d95ce97d`, verified on 2026-09-27 at
21:19:58 UTC. The earlier assembly language records historical gates, not
current pending 73 work. The subsequent 83 release did not change this
Type-valued comparison. At that checkpoint the 84 generic-restriction
successor was unaccepted and still needed changed-header CI and final review;
both subsequently completed. Accepted84 main/release-prep
`36e49294f84208fa678872e84b6bdbd96c603188` was published as official
private `e5d7d6e60243da2ec9a2af243fac3f3a3bf7dc37` on 2026-09-28
(issue #34/comment 56186). This still **unaccepted 85** successor changes
neither the Type-valued comparison body nor its original hypotheses.
Final review `abee8bb69fb0ace5d5256dc11fafcbfd2bd6485a` recorded
native4434/4435/4436 REQUEST_CHANGES for nine inherited worker-only headers,
including this pair, separate from the four earlier actual84 header repairs.
This label correction is not approval or a successor proof-integrity pass;
CI655 and CI678/679/680 on earlier inputs cannot certify changed headers.
Applicable both-target/private-inclusive checks and exact review remain.

If the frozen target or predecessor APIs change, reassess this adapter.
No source-PDF reading, passage excerpt, coverage decision, additive or
converse endpoint is claimed. The copied contributions retain Apache-2.0;
dependency rights and notices remain unchanged.
