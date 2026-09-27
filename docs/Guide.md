# Mathematical and module guide

This guide describes the shipped mathematical APIs, not a complete formalization
of a source. Import `SheafCohomology` for
the aggregate public interface, or import a subject module directly. The native
[historical API reference](API.md) supplies declaration-level displayed hypotheses
for the original 26 modules; the [AbelianForget supplement](AbelianForget.md),
[SquareTransition supplement](SquareTransition.md),
[native sheafed-space supplement](SheafedSpace.md),
[projection-mate cocone supplement](ConePullbackCocone.md),
[forgetful cocone supplement](AbelianForgetConePullbackCocone.md),
[diagram-pushforward supplement](DiagramPushforward.md),
[coefficient-diagram supplement](AbelianForgetDiagramPushforward.md),
[cone-reconstruction supplement](ConeOfPullbackCocone.md),
[native cone-limit supplement](ConePullbackLimit.md),
[limit-construction supplement](SheafedSpaceLimitConstruction.md),
[limit-preservation supplement](SheafedSpaceLimitPreservation.md),
[cofiltered coefficient-forgetting supplement](AbelianSheafedSpaceCofilteredLimits.md),
[fixed-base converse supplement](SheafedSpaceConePullbackLimitConverse.md),
[cone-pullback sections supplement](ConePullbackSections.md),
[local-pullback supplement](PullbackLocalSections.md),
[native stage-equality supplement](NativeStageSectionEquality.md),
[native stage-lifting supplement](NativeStageSectionLifting.md),
[native stage-colimit supplement](NativeStageSectionColimit.md),
[chosen native-limit global-section supplement](NativeLimitGlobalSections.md),
[native open-restriction supplement](NativeOpenRestriction.md), and
[native cylinder-limit supplement](NativeCylinderLimit.md)
cover the twenty-six new
subjects. [Generation details](README.md) identify the
old reference's exact analyzed source. The Lean
signatures and source files, rather than prose alone, determine the theorems.

## Compact opens and quasi-flasque sheaves

Evaluation on compact opens commutes with appropriate filtered colimits: the
comparison is the canonical `CategoryTheory.Limits.colimit.post` map, not merely
an unspecified isomorphism. The sheafification/section and transported
comparison lemmas make the resulting map usable in subsequent cohomology
arguments. The compact-open results require the relevant concrete-category,
prespectral/quasi-separated, filtered-diagram and sheafification assumptions;
the exact hypotheses differ across declarations.

Quasi-flasqueness concerns surjective restriction **from the terminal open to
compact opens**, not to arbitrary opens. For set-valued sheaves the categorical
definition is characterized by this surjectivity. Exactness on compact-open
sections with quasi-flasque kernel, closure under quotients and preservation by
filtered colimits require the particular space/category/universe hypotheses in
the corresponding statements. Do not infer general flasqueness or a theorem
for arbitrary coefficient categories from these results.

## Resolutions and cohomology

Degree-zero sheaf cohomology is naturally compared with global sections. The
flasque injective envelope and quasi-flasque cokernel support dimension shifting
and positive-degree acyclicity on compact prespectral quasi-separated spaces.
Separately, the functorial stalk/skyscraper flasque resolution has a
quasi-isomorphic augmentation; its terminal-open sections calculate the
positive-degree comparison. The acyclic-resolution package identifies the
degree-zero Ext complex with the complex of these sections and transports the
identification to homology. The sheaf-specific functorial construction here is
fixed at universe zero even where neighboring generic comparisons have a
universe parameter.

For an open over-site, cohomology is compared with that of the restricted sheaf,
and intrinsic restriction maps satisfy identity, composition and compatibility
with the cohomology presheaf. For a continuous map, local cohomology on its
target is the source cohomology presheaf evaluated on inverse images, followed
by sheafification. Its comparison with right-derived pushforward is **only in
positive degree** and uses a common universe for the spaces, coefficient sheaves
and Ext construction. This is not an independent-universe or degree-zero
right-derived comparison. The local-to-open, injective-resolution naturality,
and pushforward-resolution modules supply the comparison steps rather than
additional unconditional all-degree theorems.

Under the stated spectral/prespectral and quasi-separated hypotheses, the
higher-direct-image colimit result concerns every natural degree: degree zero
uses sections on compact opens and positive degree uses the local-cohomology
comparison. This *assembled* result is currently universe zero. The API also
gives the componentwise stage equation for the canonical comparison. No
sobriety, Noetherian or finite-cohomological-dimension assumption is asserted.

Pullback identity and composition comparisons include triangle identities and
triple-composition coherence; they do not identify pullback as strictly
functorial. The open-base-change construction uses the canonical inverse-image
open square, direct/inverse-image comparisons, their mate relation and counit
equation for sheaves of types. It makes no surjectivity assumption on the map.
Its space-universe bound must also hold for the coefficient category's carriers
and morphisms.

For abelian-group sheaves, the underlying-Type-sheaf functor admits a canonical
natural comparison with pullback. The arrow is **defined** by the native
Type-adjunction mate of the forgotten additive unit, is invertible for any
same-universe continuous map, and satisfies native identity and composition
laws. For any small same-universe filtered shape, forgetting preserves colimits;
the exhibited invertible comparison is the literal `colimit.post` and its
stage equation holds when both ordinary `HasColimit` instances are available.
There is no global preservation instance, spectral-space premise or new
arbitrary-universe wrapper. See [all declarations and hypotheses](AbelianForget.md).

For a commuting square and a pullback stage morphism, `SquareTransition`
constructs the canonical counit-defined transition and identifies its adjoint
with the forward strict pushforward comparison. It proves target naturality,
proof-irrelevance of square commutativity, identity, and arbitrary two-square
pasting. Its concrete-category assumptions are those of the native pullback
adjunction; space carriers, coefficient carriers and coefficient morphisms
share a universe, while the coefficient object universe is independent.
The separate `AbelianForget.SquareTransition` imports this generic API and the
canonical forgetful pullback mate. For arbitrary same-universe additive sheaves,
an arbitrary commuting square and a stage map out of `p`-pullback, it identifies
the forgotten *native* additive transition with the native Type-valued
transition on the canonically compared stage. See the
[forgetful square supplement](AbelianForget.md#commuting-squares).

## All shipped modules

The original 24 subject leaves below are included in the frozen native API
reference. Nine new `AbelianForget` leaves, `SquareTransition`,
`ConePullback`, `ConePullbackCocone`, `ConeOfPullbackCocone`, `ConePullbackLimit`,
`ConePullbackLimitConverse`, `LimitConstruction`, `LimitPreservation`, and
`DiagramPushforward`, `ConePullbackSections`, `PullbackLocalSections`,
`NativeStageSectionEquality`, `NativeStageSectionLifting`, `NativeStageSectionColimit`
and `NativeLimitGlobalSections`, `NativeOpenRestriction`, `NativeCylinderLimit`
are documented in supplements;
all 50 subjects, twenty-five client leaves and two roots form the current 77-file
Lean inventory. Prefix subject names with `SheafCohomology.`. These
descriptions identify navigation, **not** a claim that every declaration has
the same hypotheses.

| Module | Purpose |
| --- | --- |
| `AbelianForget.Basic` | Underlying Type-valued sheaf functor |
| `AbelianForget.Pullback` | Native mate, natural comparison, inverse and coherence |
| `AbelianForget.FilteredColimits` | Filtered preservation, literal comparison and stage law |
| `AbelianForget.SquareTransition` | Forgetful comparison commutes with the native square transition |
| `AbelianForget.SheafedSpace` | Forget additive structure on native sheafed spaces, preserving actual arrow mates |
| `AbelianForget.ConePullback` | Natural isomorphism between native cone pullbacks before and after additive-to-Type forgetting |
| `AbelianForget.ConePullbackCocone` | Actual projection-mate leg comparison and ordinary-colimit desc compatibility |
| `AbelianForget.LimitPreservation` | Same-universe cofiltered native limits preserved by additive-to-Type forgetting; named witnesses, no global instance |
| `AcyclicResolution` | Ext/homology comparison from acyclic resolutions |
| `ColimitPostApp` | Evaluation of canonical colimit maps at components |
| `ColimitTransport` | Transport/naturality of canonical colimit comparisons |
| `CompactOpenSections` | Compact-open section and sheafification colimits |
| `ConePullback` | Pull native sheafed-space diagrams to arbitrary cones of their underlying spaces |
| `ConePullbackSections` | Literal section units, restricted adjoint triangles and native global-section transport to the cone-pullback diagram |
| `PullbackLocalSections` | Native inverse-image stalk comparison, local representations, equality neighborhoods and finite compact-source-open covers |
| `NativeStageSectionEquality` | Literal limit-projection unit equality reflected at one native stage on compact opens and global sections |
| `NativeStageSectionLifting` | Actual cone-pullback global sections lift from native global sections after a filtered transition, using finite whole-stage descent and gluing |
| `NativeStageSectionColimit` | Named invertibility of the actual native cone-section `colimMap`, using stage equality and lifting |
| `NativeLimitGlobalSections` | Actual chosen native-limit projection cocone, section comparison, same-instance factorization and named invertibility |
| `NativeOpenRestriction` | Native restriction arrows over inverse-image opens, equality transports and actual global-section component equations |
| `NativeCylinderLimit` | Actual principal-tail native restriction diagram and its native limit, constructed from an arbitrary original native limit |
| `ConePullbackCocone` | Cocone whose legs are the mates of actual native cone projections, without a colimiting assertion |
| `ConeOfPullbackCocone` | Native cone reconstructed from actual space-cone and pullback-cocone data, with exact forgetting and transported recovery |
| `ConePullbackLimit` | Native limit criterion from the actual underlying-space limit and projection-mate sheaf colimit, with derived lifts and uniqueness |
| `ConePullbackLimitConverse` | Actual native and forgotten-base limits imply the actual projection-mate sheaf colimit, with a fixed-base Nonempty iff |
| `LimitConstruction` | Actual pullback-sheaf colimit and native limiting cone over a chosen space limit; named HasLimit witness |
| `LimitPreservation` | Named native-to-space preservation witnesses from the actual limit construction and whole-cone forgetting |
| `DegreeZero` | Degree-zero cohomology and global sections |
| `DiagramPushforward` | Native varying-base direct-image diagrams and compatible cones; stronger hypotheses only for mate formulas |
| `AbelianForget.DiagramPushforward` | Strict varying-base diagram equality, identity-vertex transported-cone isomorphism and canonical mate compatibility |
| `FilteredColimitFunctorH` | Filtered colimits for the cohomology functor |
| `FlasqueAcyclicResolution` | Flasque resolution as an Ext-acyclic resolution |
| `FlasqueAcyclicSections` | Degree-zero Ext complex and resolution sections |
| `FlasqueResolution` | Functorial flasque resolution and its augmentation |
| `HigherDirectImageFilteredColimit` | All-degree derived-image colimit theorem |
| `HigherDirectImageFilteredColimitPositive` | Positive-degree input to that theorem |
| `InjectiveResolutionNaturality` | Natural Ext comparisons for injective resolutions |
| `LocalCohomology` | Local-cohomology presheaf and sheafification |
| `LocalCohomologyFilteredColimit` | Open-over-site/compact-open colimit transport |
| `OpenBaseChange` | Canonical open square and base-change mate |
| `OpenCohomology` | Open-over-site cohomology and restrictions |
| `OpenCohomologyPushforwardResolution` | Local/pushforward-resolution comparisons |
| `OpenCohomologyRightDerived` | Positive-degree right-derived comparison |
| `PullbackCoherence` | Pullback identities, composition, and coherence |
| `QuasiFlasque` | Quasi-flasque definition and set-valued criterion |
| `QuasiFlasqueAcyclicity` | Positive-degree vanishing by dimension shift |
| `QuasiFlasqueExactness` | Exactness, quotients, filtered colimits |
| `SheafificationBasis` | Detecting sheafified isomorphisms on a basis |
| `SpectralPreimage` | Compact-open inverse image for spectral maps |
| `SquareTransition` | Canonical square transition, forward mate, naturality and arbitrary pasting |
| `SheafCohomology` | Aggregate root public imports (no new theorem) |
| `SheafCohomologyExamples` | Named downstream examples, including twenty-five imported client modules |
| `SheafCohomologyExamples.AbelianForgetPullback` | Seven private arbitrary-map, mate and coherence examples |
| `SheafCohomologyExamples.AbelianForgetFilteredColimits` | Eight private filtered-colimit and empty-space examples |
| `SheafCohomologyExamples.SquareTransition` | Eleven private Type/Ab, empty-space and arbitrary-pasting examples |
| `SheafCohomologyExamples.AbelianForgetSquareTransition` | Five private stage, target, identity, empty-space and pasted-square examples |
| `SheafCohomologyExamples.ConePullback` | Private Type/Ab Fin 3 chains, actual-arrow mates and empty-cone examples |
| `SheafCohomologyExamples.ConePullbackSections` | Five named public ordinary-import clients for literal-unit triangles, cone components, naturality and colimit legs |
| `SheafCohomologyExamples.PullbackLocalSections` | Four named public ordinary-import clients for native-unit germs, local representation, equality neighborhoods and finite germ covers |
| `SheafCohomologyExamples.NativeStageSectionEquality` | Two public ordinary-import clients: compact-open and native global-section distinguishability |
| `SheafCohomologyExamples.NativeStageSectionLifting` | Two private ordinary-import clients: eventual native-section inhabitation and persistence of a lift along later arrows |
| `SheafCohomologyExamples.NativeStageSectionColimit` | Two private ordinary-import clients: cancellation of the actual comparison and recovery of a target coprojection through its local inverse |
| `SheafCohomologyExamples.NativeLimitGlobalSections` | Private ordinary-import client: actual native projection images detect coprojection equality |
| `SheafCohomologyExamples.NativeOpenRestriction` | Private ordinary-import client: compose two restricted native arrows and recover the original composite's section component |
| `SheafCohomologyExamples.NativeCylinderLimit` | Private ordinary-import client: apply the constructed restricted limit to an arbitrary cone and recover the original native projection equation |
| `SheafCohomologyExamples.ConePullbackCocone` | Private Type/Ab native cone triangles, empty-carrier cone and conditional colimit.desc |
| `SheafCohomologyExamples.ConeOfPullbackCocone` | Private Type/Ab Fin 3 projections, mates and cone equations; transported recovery and arbitrary-sheaf empty-index clients |
| `SheafCohomologyExamples.ConePullbackLimit` | Private Type/Ab Fin 3 lifts, projections and mates; empty-index reconstruction conditional on a genuine sheaf-colimit witness |
| `SheafCohomologyExamples.ConePullbackLimitConverse` | Private Type/Ab arbitrary-cocone descent, factorization and uniqueness; independent shape universes and a separately supplied empty native limit |
| `SheafCohomologyExamples.LimitConstruction` | Private Type/Ab Fin 3 limiting cones and actual colimit-leg readbacks; genuine empty-index limit with a constructed initial sheaf |
| `SheafCohomologyExamples.LimitPreservation` | Private Type/Ab Fin 3 and empty-shape preservation on arbitrary limiting cones; chosen comparison and projection laws |
| `SheafCohomologyExamples.AbelianForgetSheafedSpace` | Private native arrow, chain, identity and empty-carrier examples |
| `SheafCohomologyExamples.AbelianForgetConePullback` | Private cone-wise components, index-arrow naturality and actual empty-vertex cone |
| `SheafCohomologyExamples.AbelianForgetConePullbackCocone` | Private native Fin 3 stages/triangles, desc compatibility, local filtered comparison and empty-carrier clients |
| `SheafCohomologyExamples.DiagramPushforward` | Private Type/Ab Fin 3 stages, mates, compositions and compatible native cones, plus empty-index cones with arbitrary vertex map |
| `SheafCohomologyExamples.AbelianForgetDiagramPushforward` | Twelve private coefficient-diagram clients: nonidentity Fin 3 arrows and composition, compatible projections and empty-index cones |
| `SheafCohomologyExamples.AbelianForgetLimitPreservation` | Private finite, natural-number and polymorphic preservation clients; separate mapped-cone composition laws |

## Using the boundary

The native cone-limit criterion takes the universal properties of the actual
forgotten space cone and actual projection-mate sheaf cocone; it does not
assume the native limit it proves. The coefficient category must satisfy the
concrete-category, limits/colimits and forgetful preservation/reflection
hypotheses of the native pullback adjunction. The index object and morphism
universes are independent. That criterion alone supplies neither a sheaf colimit
nor a global `HasLimits` instance or Ringed/coefficient-changing extension.
The separate [limit-construction supplement](SheafedSpaceLimitConstruction.md)
supplies the actual sheaf colimit using coefficient shape-colimits and weak
sheafification at the chosen vertex, explicitly installing the existing
site-sheaf colimit instance locally for the `TopCat.Sheaf` wrapper. It constructs
the native limit, with exact base and projection-mate readbacks, and a named
`HasLimit` witness over a selected base limit. Its empty-index client constructs
the sheaf colimit and initial sheaf rather than assuming them. This is not a
global instance or a result for all unrestricted large diagrams; the explicit
shape-colimit and sheafification hypotheses remain essential.

The [fixed-base converse supplement](SheafedSpaceConePullbackLimitConverse.md)
instead takes both the actual native limiting witness and the actual forgotten
space-cone limiting witness. It derives the universal property of the actual
projection-mate cocone, not the existence of arbitrary sheaf colimits. Its iff
uses the forward criterion for the other direction. No shape-filteredness or
local weak-sheafification premise is added; native concrete-coefficient
assumptions remain. Empty-shape clients separately supply a genuine native
limit rather than infer it merely from a terminal underlying space.

The [limit-preservation supplement](SheafedSpaceLimitPreservation.md) uses
that genuine construction and equality of its whole forgotten cone to prove
ordinary `PreservesLimit` for the native-to-space functor. Its two named
witnesses retain the construction's hypotheses, either over a supplied space
limit or at the chosen space-limit vertex. They do not assume the desired
native limit, register a global instance, reflect limits or compare coefficient
forgetting. Private clients apply ordinary preservation to arbitrary native
limiting cones and use the chosen-limit projection comparison.

The [cofiltered coefficient-forgetting supplement](AbelianSheafedSpaceCofilteredLimits.md)
uses filtered sheaf-colimit preservation on the actual cone vertex, the
cone-wise diagram isomorphism and every projection-mate leg to transport the
colimiting cocone. For a same-universe small filtered `J`, the resulting named
preservation witnesses apply to all additive native diagrams on `Jᵒᵖ` and all
their limiting cones. The chosen-space-cone helper states its local weak
sheafification hypothesis. No arbitrary or empty-shape preservation, reflection
or global instance follows. Three private clients genuinely use a supplied
native limiting witness; their separate composition equations are ordinary
mapped-cone `.w` laws and hold even without that witness.

The [cone-pullback sections supplement](ConePullbackSections.md) concerns
Type-valued sheaves on spaces in the same universe and an arbitrary small
index category. Its restricted triangle identifies the actual adjunction unit
and restrictions on arbitrary opens. The natural transformation has domain
exactly `N.rightOp` composed with native global sections, not a separately
postulated stage system. Its ordinary `colimMap` stage law requires just the
two indicated individual colimits. No limiting, spectral, filtered or nonempty
assumption is used, and no IsIso, finite-stage equality or gluing follows here.

The [local-pullback supplement](PullbackLocalSections.md) concerns the actual
inverse-image sheaf and adjunction unit for any map of same-universe spaces
and Type-valued sheaf. Stalk comparison, local representation and equality
reflection require no compactness, spectrality, surjectivity or inhabitance.
Only the finite local representation theorem requires a prespectral source
and a compact source open; its target opens need not be compact. No global
section surjectivity, stage equality, gluing or colimit endpoint is claimed.

The [native stage-equality supplement](NativeStageSectionEquality.md) separately
proves eventual equality for the actual projection unit of a limiting
underlying-space cone. It uses a same-universe small filtered category,
Type-valued native sheafed spaces with spectral underlying spaces, and spectral
transition maps. Equality on the inverse image of a compact stage open is
reflected by one native transition on that entire inverse-image open at the
later stage. The whole-space specialization uses exactly `N.rightOp` composed
with `SheafedSpace.Γ`. Neither inhabited stages nor surjective transitions are
assumed. The proof combines native local-unit equality neighborhoods with the
published spectral cylinder criterion; no gluing, finite simultaneous equality,
colimit-map invertibility or source coverage follows from this leaf alone.

The [native stage-lifting supplement](NativeStageSectionLifting.md) uses the
same spectral-limit hypotheses to lift every global section of the actual
cone-pullback sheaf to a native global section at a later stage. Its equation
uses the literal `ConePullbackSections.coneSections` component and actual
cone-pullback transition. Finite local representations, whole-stage cylinder
descent, coherent overlap synchronization and sheaf gluing prove the lift;
no nonempty-stage or nonempty-cover hypothesis is added. This element-level
theorem does not itself assert a filtered-colimit comparison or endpoint IsIso.

The [native stage-colimit supplement](NativeStageSectionColimit.md) then proves
`AlgebraicGeometry.SheafedSpace.isIso_colimMap_coneSections` under those
same-universe small filtered, actual-limit and spectral-stage/map hypotheses.
Its map is literally `colimMap (ConePullbackSections.coneSections N c)`, from
the colimit of `N.rightOp` composed with native `SheafedSpace.Γ` to the colimit
of top-open sections of the actual cone-pullback diagram. Filtered equality
and native stage equality prove injectivity; native lifting and the actual
stage-leg equation prove surjectivity. No transition injectivity, inhabitance
or desired-isomorphism premise is added, and the theorem is not a global
instance. Two private clients cancel this map and use its locally installed
inverse. It does not identify global sections of a chosen native limit,
prove a source square endpoint, or extend the result to additive coefficients.

The [chosen native-limit global-section supplement](NativeLimitGlobalSections.md)
supplies that separate comparison for
`Q = limitConeOfSpaceCone (Type v) N c hc`.
`AlgebraicGeometry.SheafedSpace.nativeGlobalSectionsCocone` has Q's actual
native projection maps under `Γ` as legs; `nativeGlobalSectionsComparison`
is its literal `colimit.desc`. The stage law and
`nativeGlobalSectionsComparison_eq_colimMap_post` identify the factorization
through moving-stage sections and fixed-base top-open evaluation using the
same local sheaf-colimit instance as Q. Under the same-universe small filtered,
actual-limit and spectral-stage/map hypotheses,
`isIso_nativeGlobalSectionsComparison` proves invertibility without a global
instance or assumed comparison. A private ordinary-import client detects
coprojection equality by actual projection images. Source square endpoints,
additive extensions and arbitrary colimit-choice identifications are not added.

The [open-restriction supplement](NativeOpenRestriction.md) uses existing
native inclusions and mathlib's open-immersion lift, with explicit named-open
and iterated inverse-image equality transports. Its same-universe Type-valued
section readback needs no compactness, spectrality, limiting cone or inhabited
open. Its private client composes two restricted arrows and recovers the
original composite's section component. It supplies no principal-tail or
cylinder-limit theorem.

The separate [native cylinder-limit supplement](NativeCylinderLimit.md) constructs
that principal-tail diagram and limit. For `ι : Type v` with a directed preorder,
an explicit `i0 : ι`, `N : ιᵒᵖ ⥤ SheafedSpace.{v+1,v,v} (Type v)`, an
arbitrary native limiting cone `m` and an open at `i0`, `restrictedIsLimit`
proves that `restrictedCone` is limiting over the actual diagram `restricted`.
The original limit is input; a limit of the restricted diagram is constructed,
not assumed. Finality of the principal tail, the native open-immersion lift and
monic cancellation give existence and uniqueness. No linear order, spectrality
or nonempty-space/open hypothesis is needed. The private ordinary-import client
uses this constructed limit for any restricted cone, then recovers the original
projection equation after the native inclusion. This unit adds no chosen-limit
isomorphism, section comparison for the restricted diagram or spectral transfer.

The `SheafCohomologyExamples` target demonstrates the intended imports
for compact-open colimits, quasi-flasqueness, the resolution interfaces, local
cohomology, higher direct images, open base change and native section transport.
At the original 2026-09-27 19:11:29 UTC assembly, the 77-module aggregate's
combined build and private-inclusive axiom evidence was still outstanding.
The full aggregate CI590 check on `c2809532ab73025867cb24b8b80d9e67da069d2d`
succeeded at 20:37:50 UTC that day, and the owner subsequently inspected its
complete evidence. That evidence applies to this documentation-only successor
because all computational inputs are unchanged; this records evidence reuse,
not a fresh build or audit on the successor. The current required CI context,
independent final review and individual owner/release decisions are separate
gates. Predecessor and focused leaf checks apply only to their recorded inputs.
Private example names are not public
API, including the native stage-lifting, stage-colimit, chosen native-limit and
open-restriction and cylinder-limit clients;
the section-transport,
local-pullback and native stage-equality clients are public named examples. Inspect the sample's
actual binders when adapting a result:
the positive/zero-degree split and universe-zero restrictions are essential.
Review actual source hypotheses and typeclass instances rather than guessing
them from the abstract's subject labels. External research records are not
required to build or import this library.
