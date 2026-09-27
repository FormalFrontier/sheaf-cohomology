# Cofiltered native limits after forgetting additive sheaf coefficients

Import `SheafCohomology.AbelianForget.LimitPreservation` directly. For
`J : Type v` with `[SmallCategory J]` and `[IsFiltered J]`, and any
`S : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace AddCommGrpCat.{v}`, the named
`SheafedSpace.AbelianForget.preservesCofilteredLimit S` provides
`PreservesLimit S SheafedSpace.AbelianForget.underlying`. There is also a named
`preservesCofilteredLimitsOfShape` witness for the same `Jᵒᵖ`; neither is a
global instance. Both preserve **all** limiting native cones over `S`, not
merely a conveniently chosen limit.

The aggregate `SheafCohomology` root also re-exports this producer, and
`SheafCohomologyExamples` imports the private client module below. Root
registration alone does not certify the combined graph or its publication.

For example, given `C : Cone S` and `hC : IsLimit C`:

```lean
letI : PreservesLimit S SheafedSpace.AbelianForget.underlying :=
  SheafedSpace.AbelianForget.preservesCofilteredLimit S
exact isLimitOfPreserves SheafedSpace.AbelianForget.underlying hC
```

## Proof and actual cones

Given an actual additive cone `C`, its inverse-image sheaf diagram
`conePullback AddCommGrpCat S ((forget AddCommGrpCat).mapCone C)` is indexed
**covariantly by `J`**, hence filtered. On the real base `(C.pt : TopCat)`,
`preservesFilteredSheafColimit` transports any colimiting additive projection-
mate cocone through `underlyingSheaf`. The `conePullbackIso` identifies its
diagram with the actual Type pullback diagram. Mathlib's
`IsColimit.precomposeHomEquiv` transports the colimit witness across this
natural isomorphism; `conePullbackCocone_forget_ι` identifies *every* actual
Type projection-mate leg, not just the cocone point. The public helper
`isColimit_conePullbackCocone_underlying S C hK` packages exactly this step.

For a chosen genuine `hc : IsLimit c` of the underlying-space diagram,
`limitConeOfSpaceCone AddCommGrpCat S c hc` supplies a native `LimitCone`.
Its sheaf is the **actual** site-sheaf colimit constructed locally by
`conePullbackColimitCocone`; this colimit is proved by
`conePullbackColimitCocone_isColimit`, not assumed. Its actual projection
mates recover those colimit legs by `coneOfPullbackCocone_π_mate` (the
whole-cocone transport law is `conePullbackCocone_coneOfPullbackCocone`).
The native forgotten base cone has exactly the chosen vertices and projections:
the producer's `change` uses this definitional identification of diagrams,
and the cocone isomorphism identifies the actual projection mates. The Type
criterion `isLimit_of_isLimit_forget_of_isColimit_conePullbackCocone` therefore
proves the *forgotten native cone* is limiting. Finally,
`preservesLimit_of_preserves_limit_cone` lifts that one genuine constructed
limiting cone to arbitrary limiting cones over the same diagram.

`preservesLimit_fromSpaceCone S c hc` exposes this intermediate chosen-base
proof with the exact local `[HasWeakSheafify
(Opens.grothendieckTopology c.pt) AddCommGrpCat.{v}]` requirement.
`preservesCofilteredLimit` chooses the ordinary TopCat base limit, inferring
the concrete colimit and sheafification instances. No `PreservesColimit`
assumption, hypothetical native preservation, or `IsLimit` of the desired
forgotten cone is a public premise.

## Reproduction and boundaries

`SheafCohomologyExamples.AbelianForgetLimitPreservation` imports only the
producer. Its private `finitePreserved`, `natPreserved`, and
`polymorphicPreserved` clients really use the local preservation witness
and an additive limiting-cone hypothesis `hC` to obtain the forgotten
`IsLimit`. Its separate finite and natural-number `finiteComposite` and
`natComposite` examples assert mapped-cone `.w` laws: these equalities hold
for **any cone**, independently of `hC` or the preservation witness. The
existing clients retain their original proofs for source-exact transfer;
their use of `hC` in those two examples is not mathematically necessary.
The three-stage and infinite clients use nonidentity **index arrows** and
their composites for arbitrary diagrams, without claiming that every
diagram sends those arrows to nonidentity morphisms.

In the repository-pinned Lean/Lake environment, fetch the matching mathlib
cache *before* focused checks:

```sh
LAKE_JOBS=1 LEAN_NUM_THREADS=2 lake exe cache get
LAKE_JOBS=1 LEAN_NUM_THREADS=2 lake --no-ansi --wfail build SheafCohomology.AbelianForget.LimitPreservation SheafCohomologyExamples.AbelianForgetLimitPreservation
```

The **same-universe** `SmallCategory J` and `IsFiltered J` match the filtered
sheaf-colimit theorem. A nonempty filtered index is essential: the additive
initial sheaf required by an empty native limit generally does not remain
initial after forgetting its group structure. No preservation of empty or
arbitrary native limits, creation/reflection of limits, or source coverage
follows from this API. It reuses
`SheafCohomology.AbelianForget.FilteredColimits`,
`SheafCohomology.AbelianForget.ConePullbackCocone`, and
`SheafCohomology.LimitConstruction` as direct prerequisites; it has no
incubator or unpublished deliverable dependency.

## Provenance and lifecycle

Original expression author: Worker B, Hive Task
`hive-request-13fb7168e78b10adc0a739488a5b88a5bad2cd58`, UID
`9a8d7368-37db-444c-b740-2b889ce82678`, incubator leaf
`bca0b7e2157ff42e7fee82a844a24ed64bd81957`. Fresh original reviewer:
Worker A, Hive Task `hive-request-e191e9001fd91ccc94ac716347cfe494151b243a`,
UID `e456f556-7b89-45ca-a633-7c5641bb1484`, exact review
`012dbb7d96b8692316e94ba000e5d85108222cf2`. Anchor accepted only
that leaf in incubator issue 4 comment 51036. Its native constructor
prerequisite `f30d2befa872ce170736d97a72444790847365e5` was accepted
but unregistered at that point; its own author and reviewer retain credit.

Destination transfer adapter (not the mathematical author): Worker A, distinct
Hive Task `hive-request-e5601633e037e2e255c65a2ce615260dafca7b25`,
UID `08e5a83e-3ade-46bf-8ef3-64545240ab1c`. The destination branch begins
at frozen sheaf-cohomology `9264d1e7569dfe2ab4b026490c45cf39805c7f79`,
an **unreviewed, unaccepted** 57-module registration with no combined check.
Anchor's source-only 59-module registration preserves both Lean leaf blobs
and every dependency and CI input; only aggregate imports, navigation, credit
and lifecycle metadata are added. The 57-module base remains unaccepted,
and its 55-module ancestor still awaits successful applicable evidence. The
exact three-file adapter received a separate scoped approval from fresh
Worker B Task `hive-request-50aefd26f24f869e97ac447c866866dfd7b401e5`, UID
`eec8c8c6-7bf7-415d-a65a-0158821d942d`, report
`bf34ba8739f38b4196c7b6bc85ed778560efce2a`. That report-only verdict covers
neither this registration nor its inherited graph; it is not a native PR vote.
Fresh registered-graph and release review, applicable combined checks, owner
acceptance and integration, individually verified official release, and finally
a reviewed incubator conversion to that exact published dependency remain
separate steps. No combined build or private-inclusive axiom pass is claimed
for this registration. Until then this branch is not a released API.
