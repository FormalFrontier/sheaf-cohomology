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

## Clients and boundaries

`SheafCohomologyExamples.AbelianForgetLimitPreservation` imports only the
producer. Its private `finitePreserved`, `natPreserved`, and
`polymorphicPreserved` clients really use the local preservation witness
and an additive limiting-cone hypothesis `hC` to obtain the forgotten
`IsLimit`. Its separate finite and natural-number `finiteComposite` and
`natComposite` examples assert mapped-cone `.w` laws: these equalities hold
for **any cone**, independently of `hC` or the preservation witness. Their
use of `hC` in those two examples is not mathematically necessary.
The three-stage and infinite clients use nonidentity **index arrows** and
their composites for arbitrary diagrams, without claiming that every
diagram sends those arrows to nonidentity morphisms.

The small filtered index is nonempty. The initial additive sheaf of
an empty native limit generally does not remain initial on forgetting
its group structure. This does not preserve arbitrary or empty limits,
create or reflect limits, or make a source-coverage claim.
