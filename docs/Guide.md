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
[diagram-pushforward supplement](DiagramPushforward.md), and
[coefficient-diagram supplement](AbelianForgetDiagramPushforward.md) cover the twelve new
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
reference. Eight new `AbelianForget` leaves, `SquareTransition`,
`ConePullback`, `ConePullbackCocone`, and `DiagramPushforward` are documented in supplements;
all 36 subjects and thirteen roots/clients form the current 49-file
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
| `AcyclicResolution` | Ext/homology comparison from acyclic resolutions |
| `ColimitPostApp` | Evaluation of canonical colimit maps at components |
| `ColimitTransport` | Transport/naturality of canonical colimit comparisons |
| `CompactOpenSections` | Compact-open section and sheafification colimits |
| `ConePullback` | Pull native sheafed-space diagrams to arbitrary cones of their underlying spaces |
| `ConePullbackCocone` | Cocone whose legs are the mates of actual native cone projections, without a colimiting assertion |
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
| `SheafCohomologyExamples` | Named private downstream examples, including eleven imported client modules |
| `SheafCohomologyExamples.AbelianForgetPullback` | Seven private arbitrary-map, mate and coherence examples |
| `SheafCohomologyExamples.AbelianForgetFilteredColimits` | Eight private filtered-colimit and empty-space examples |
| `SheafCohomologyExamples.SquareTransition` | Eleven private Type/Ab, empty-space and arbitrary-pasting examples |
| `SheafCohomologyExamples.AbelianForgetSquareTransition` | Five private stage, target, identity, empty-space and pasted-square examples |
| `SheafCohomologyExamples.ConePullback` | Private Type/Ab Fin 3 chains, actual-arrow mates and empty-cone examples |
| `SheafCohomologyExamples.ConePullbackCocone` | Private Type/Ab native cone triangles, empty-carrier cone and conditional colimit.desc |
| `SheafCohomologyExamples.AbelianForgetSheafedSpace` | Private native arrow, chain, identity and empty-carrier examples |
| `SheafCohomologyExamples.AbelianForgetConePullback` | Private cone-wise components, index-arrow naturality and actual empty-vertex cone |
| `SheafCohomologyExamples.AbelianForgetConePullbackCocone` | Private native Fin 3 stages/triangles, desc compatibility, local filtered comparison and empty-carrier clients |
| `SheafCohomologyExamples.DiagramPushforward` | Private Type/Ab Fin 3 stages, mates, compositions and compatible native cones, plus empty-index cones with arbitrary vertex map |
| `SheafCohomologyExamples.AbelianForgetDiagramPushforward` | Twelve private coefficient-diagram clients: nonidentity Fin 3 arrows and composition, compatible projections and empty-index cones |

## Using the boundary

The checked `SheafCohomologyExamples` target demonstrates the intended imports
for compact-open colimits, quasi-flasqueness, the resolution interfaces, local
cohomology, higher direct images and open base change. Private example names
are not public API. Inspect the sample's actual binders when adapting a result:
the positive/zero-degree split and universe-zero restrictions are essential.
Review actual source hypotheses and typeclass instances rather than guessing
them from the abstract's subject labels. External research records are not
required to build or import this library.
