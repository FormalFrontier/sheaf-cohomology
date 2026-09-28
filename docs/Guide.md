# Mathematical and module guide

This guide describes the accepted library and the proposed ring transfer,
not a complete formalization of a source. On an accepted release import
`SheafCohomology` for
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
[native open-restriction supplement](NativeOpenRestriction.md),
[native cylinder-limit supplement](NativeCylinderLimit.md),
[native cylinder-comparison supplement](NativeCylinderComparison.md),
[native spectral-cylinder sections supplement](NativeSpectralCylinderSections.md),
[native additive global-sections supplement](NativeAdditiveGlobalSections.md),
[native additive-cylinder sections supplement](NativeAdditiveCylinderSections.md),
[ring coefficient-forgetting guide](CommRingForget.md), and
[ring global-sections guide](NativeCommRingGlobalSections.md)
cover both the older additions and the proposed ring subjects.
[Generation details](README.md) identify the
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

The ring-to-Type functor has analogous native mates and filtered sheaf colimits;
for a small same-universe filtered shape it preserves actual native cofiltered
limits without a global instance or spectral hypothesis. Given an *original*
spectral native limit, the ring global-section comparison uses its literal
projection maps, is invertible, and gives a stage representative for each
section (not surjectivity at any fixed stage). See the
[ring bridge](CommRingForget.md) and [endpoint](NativeCommRingGlobalSections.md)
for the exact assumptions and empty-index boundary.

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

## Accepted and proposed modules

The original 24 subject leaves below are included in the frozen native API
reference. Nine new `AbelianForget` leaves, `SquareTransition`,
`ConePullback`, `ConePullbackCocone`, `ConeOfPullbackCocone`, `ConePullbackLimit`,
`ConePullbackLimitConverse`, `LimitConstruction`, `LimitPreservation`, and
`DiagramPushforward`, `ConePullbackSections`, `PullbackLocalSections`,
`NativeStageSectionEquality`, `NativeStageSectionLifting`, `NativeStageSectionColimit`
and `NativeLimitGlobalSections`, `NativeOpenRestriction`, `NativeCylinderLimit`,
`NativeCylinderComparison`, `NativeSpectralCylinder`,
`NativeSpectralCylinderSections`, `NativeAdditiveGlobalSections`, and
`NativeAdditiveCylinderSections`
are documented in supplements;
the earlier 55 subjects, thirty-one client leaves and two roots form the
accepted 88-file baseline. The present candidate adds seven `CommRingForget`
subjects and one `NativeCommRingGlobalSections` subject, one example leaf,
and keeps the two roots: 63 producer leaves, 32 example leaves, 97 Lean files.
The stage-representative theorem is inside the endpoint producer, not a separate
example leaf. Prefix producer subject names with `SheafCohomology.`. These
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
| `CommRingForget.Basic` | Underlying Type-valued sheaf of a commutative-ring sheaf |
| `CommRingForget.Pullback` | Canonical original-unit pullback mate and invertible natural comparison |
| `CommRingForget.FilteredColimits` | Literal filtered sheaf-colimit comparison and stage equation |
| `CommRingForget.SheafedSpace` | Native commutative-ring-to-Type coefficient-forgetting functor |
| `CommRingForget.ConePullback` | Original-cone pullback diagram comparison |
| `CommRingForget.ConePullbackCocone` | Comparison of the actual projection-mate cocone legs |
| `CommRingForget.LimitPreservation` | Same-universe cofiltered native-limit preservation, without global instance |
| `NativeCommRingGlobalSections` | Original-cone ring-section cocone, isomorphism under spectral hypotheses, joint-stage representative |
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
| `NativeOpenRestriction` | Category-generic native restriction arrows over inverse-image opens, equality transports and actual global-section component equations |
| `NativeCylinderLimit` | Actual principal-tail native restriction diagram and its native limit, constructed from an arbitrary original native limit |
| `NativeCylinderComparison` | Chosen native-limit isomorphism, projection/base laws and actual original-stage section comparison with both equality transports |
| `NativeSpectralCylinder` | Coefficient-generic spectrality of literal restricted stages and maps from compact possibly-empty opens; no cone/limit input |
| `NativeSpectralCylinderSections` | Invertibility of that comparison on compact-open cylinders of original spectral stages and spectral transition maps |
| `NativeAdditiveGlobalSections` | Original additive cone-section cocone, comparison and literal stage law, with named invertibility for an actual native spectral limit |
| `NativeAdditiveCylinderSections` | Additive comparison and both original-arrow laws on a preorder; locally filtered IsIso after constructing the native restricted limit |
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
| `SheafCohomologyExamples` | Named downstream examples, including thirty-one imported client modules |
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
| `SheafCohomologyExamples.NativeOpenRestrictionAdditive` | Named private ordinary-import additive client: the same composition readback with the explicit inverse-image cast |
| `SheafCohomologyExamples.NativeCylinderLimit` | Private ordinary-import client: apply the constructed restricted limit to an arbitrary cone and recover the original native projection equation |
| `SheafCohomologyExamples.NativeCylinderLimitAdditive` | Private ordinary-import additive client: apply the same constructed generic restricted limit and recover the original native projection equation |
| `SheafCohomologyExamples.NativeCylinderComparison` | Private ordinary-import client: inverse native projection law, both base identities and the original-stage section equation for arbitrary opens |
| `SheafCohomologyExamples.NativeSpectralCylinderSections` | Private ordinary-import client: cancel the actual comparison on original-stage sections, retaining both equality transports |
| `SheafCohomologyExamples.NativeAdditiveGlobalSections` | Private ordinary-import client: original additive projection equality iff equality after an actual later original-stage transition |
| `SheafCohomologyExamples.NativeAdditiveCylinderSections` | Named private ordinary-import client: actual original-projection equality detects additive coprojection equality with both casts |
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
| `SheafCohomologyExamples.CommRingForgetLimitPreservation` | Named public `uniqueLift` ordinary-import example for original forgotten projections |

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
and iterated inverse-image equality transports. For
`{C : Type (v + 1)} [Category.{v} C]` and `SheafedSpace.{v+1,v,v} C`, its
section readback needs no concrete coefficients, extra limits, compactness,
spectrality, limiting cone or inhabited open. Its Type and named private
additive clients compose two restricted arrows and recover the original
composite's section component. These specialize the same declarations;
no parallel Type implementation is added. This unit supplies no principal-tail
or cylinder-limit theorem.

The separate [native cylinder-limit supplement](NativeCylinderLimit.md) constructs
that principal-tail diagram and limit. For `ι : Type v` with a directed preorder,
an explicit `i0 : ι`, `C : Type (v + 1)` with `Category.{v} C` inferred from
`N : ιᵒᵖ ⥤ SheafedSpace.{v+1,v,v} C`, an
arbitrary native limiting cone `m` and an open at `i0`, `restrictedIsLimit`
proves that `restrictedCone` is limiting over the actual diagram `restricted`.
The original limit is input; a limit of the restricted diagram is constructed,
not assumed. Finality of the principal tail, the native open-immersion lift and
monic cancellation give existence and uniqueness. No linear order, spectrality
or nonempty-space/open hypothesis is needed. Separate Type and additive private
ordinary-import clients use the same constructed generic limit for any restricted
cone, then recover the original projection equation after the native inclusion;
there is no duplicate Type wrapper. This unit adds no chosen-limit
isomorphism, section comparison for the restricted diagram or spectral transfer.

The separate [native cylinder-comparison supplement](NativeCylinderComparison.md)
constructs the chosen-limit isomorphism and section comparison for that diagram.
It uses native-to-space limit preservation to obtain the actual forgotten limit,
then uniqueness of native limits for the chosen isomorphism. Both native projection
equations and both underlying identity-map laws are proved. The section comparison
uses `Γ.map` of the inverse isomorphism, with a restriction-object cast; its stage
law recovers the original native projection's presheaf component with the named
inverse-image cast. The same directed preorder, explicit index, actual original
native limit and arbitrary open suffice; no spectrality or nonempty-open assumption
is added. Its genuine private ordinary-import client uses all these laws together.
No spectral invertibility of this restricted comparison is asserted by this unit.

The [native spectral-cylinder sections supplement](NativeSpectralCylinderSections.md)
separately proves that invertibility. It assumes spectral original stages and
spectral original transition maps and a compact chosen stage open, alongside
the directed preorder, explicit index and genuine original native limit.
Compact-open inverse images give spectral restricted stages. The actual native
inclusion square and the published subtype criterion give spectral restricted
arrows. Public colimit-leg equations identify the existing comparison with the
native global-sections comparison followed by inverse/op and restriction casts;
each factor is invertible. No desired isomorphism, restricted-limit premise,
surjectivity or nonempty-open assumption is added. The private ordinary-import
client detects equality of transported stage coprojections by actual original
projection sections, keeping both the restriction-object and named-open casts.

The [native additive global-sections supplement](NativeAdditiveGlobalSections.md)
defines the section cocone of any original additive cone, its `colimit.desc`
comparison and literal original-projection stage law, without filteredness or
limit assumptions for those definitions/law. For a small same-universe filtered
diagram, an actual original native limit and spectral original stages/maps,
the comparison is an isomorphism. The proof uses full cone/diagram forgetting,
the actual native projection law and forward `colimit.post`, then reflects
isomorphisms of additive groups. Its ordinary-import client derives eventual
equality from original projection equality rather than assuming it. This is
an additive global-sections result, not an additive compact-cylinder extension.

The [native additive-cylinder sections supplement](NativeAdditiveCylinderSections.md)
also documents the coefficient-generic `NativeSpectralCylinder` helper. For any
coefficient category its literal restricted stages and arrows are spectral
when the original stages/maps are spectral and the chosen open is compact,
even when that open is empty; no cone or limit is required for this transfer.
The additive comparison and **both** full `AddCommGrpCat` arrow laws use the
original cone on a preorder alone. For an actual original native limit, tail
directedness/filteredness are introduced only locally, the restricted native
limit is constructed rather than assumed, and spectrality gives its `IsIso`.
The named private ordinary-import client cancels on actual original projection
sections with both restriction-object and named-open casts.

The `SheafCohomologyExamples` target demonstrates the intended imports
for compact-open colimits, quasi-flasqueness, the resolution interfaces, local
cohomology, higher direct images, open base change and native section transport.
The original 2026-09-28 source-only 88-module registration starts from static adapter
`a476ccbaf62a401b1cc8b464bfe04da27dfab46e` on frozen **unaccepted** parent
`651f8223c7dbb2df870f3f594077365bf6767d7f`. The two public producer
imports and one ordinary private-client import change the aggregate roots;
all 86 nonroot Lean blobs and eleven complete dependency objects remain fixed.
At the 02:31 UTC owner checkpoint, actual 79 was privately published and final
81 CI648 was owner-intaken without acceptance/release; actual 85 CI655 supplied
metadata-only evidence, not yet owner-intaken. None then certified the changed
88 graph; ordered 81→83→84→85 releases remained separate.

The frozen 88 head `1ded7c974bdb6cd753e393fbc8d09bb2782c69e9`
subsequently passed full both-target/private-inclusive CI665/artifact121236
(owner intake #34/55987), and its mathematical/API/provenance/registration
scope was independently approved at `eed9f975efd4dd17cbace2d3a40d4d041319b67f`
(native4411, owner intake #34/55894). Neither is a metadata-only pass or
acceptance of the changed-header actual-parent 88 successor.

At its original 2026-09-28 assembly, the source-only 85-module aggregate had
no combined build or private-inclusive axiom evidence. Donor seven-module
evidence and old 84 CI637/artifact112464 did not certify its changed closure.
Frozen 85 `651f8223c7dbb2df870f3f594077365bf6767d7f` subsequently passed
full both-target/private-inclusive CI655 (issue #34/comment 55824); scoped
review first requested a collective-credit correction (native4404) and then
approved the exact repaired original (native4405). Actual 81 and 83 each
completed their own official release at `b743039857ca8c206b6a8cdb99afe7c7e8ce0c25`
and `6793f2ff8469d1cab23a98ac2da22a3286d22f8e`, respectively. Full
changed-header CI674 and independent final review supported actual accepted 84
main/release-prep `36e49294f84208fa678872e84b6bdbd96c603188` and private
release `e5d7d6e60243da2ec9a2af243fac3f3a3bf7dc37`, verified on 2026-09-28
(issue #34/comment 56186). At that dated checkpoint the **unaccepted 85** successor merged actual
84 main ancestry and inherits four reversible collective-credit headers. Final
review `abee8bb69fb0ace5d5256dc11fafcbfd2bd6485a` requested changes on
PR141/147/148 (native4434/4435/4436) for nine further inherited worker-only
author headers, not for the unchanged mathematics or fourteen headerless files.
That successor repaired those nine labels; 13 headers differ from frozen 85,
while every module-onward byte remains fixed. Neither original CI655 nor the
CI678/679/680 executions on the prior candidate certify these changed inputs.
At that checkpoint, applicable 85 evidence and fresh independent review
remained; the header repair alone was not an approval or acceptance.
Subsequent full CI685/artifact131785, author-distinct consolidated review
`fc9bb966ca2c9f9426fd817341f787e851351bcd` (native4442–4444), separate
owner gates and protected integrations completed actual 85: accepted main
`25e596baca25cf582aa2f6d9ba22d7833de74ec7`, official private release
`2c7b5e3e2e94704b9aa825c1aed88a880cf78dae` (#34/56450).
This still **unaccepted 88** successor merges the accepted 85 development
commit into frozen 88, inheriting 13 complete collective-credit headers but
preserving all 88 Lean module-onward bodies, imports, options and both roots.
Neither original full CI665 nor 85 CI685 checks the thirteen changed 88-header
inputs. Applicable both-target/private-inclusive successor 88 CI and a fresh
author-distinct consolidated final main/prep/public review remain before
separate owner acceptance, protected integration and verified publication;
neither source coverage nor incubator conversion follows.
Private example names are not public API, including the native stage-lifting,
stage-colimit, chosen native-limit and
Type/additive open-restriction, Type/additive cylinder-limit, cylinder-comparison,
spectral-cylinder and additive clients; the section-transport, local-pullback
and native stage-equality clients are public named examples. Inspect the sample's
actual binders when adapting a result:
the positive/zero-degree split and universe-zero restrictions are essential.
Review actual source hypotheses and typeclass instances rather than guessing
them from the abstract's subject labels. External research records are not
required to build or import this library.
