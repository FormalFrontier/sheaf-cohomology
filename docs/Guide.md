# Mathematical and module guide

This guide describes the shipped mathematical APIs, not a complete formalization
of a source. Import `SheafCohomology` for
the aggregate public interface, or import a subject module directly. The native
[API reference](API.md) supplies declaration-level displayed hypotheses and
[generation details](README.md) identify its exact analyzed source. The Lean
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

## All shipped modules

Every subject leaf below is included in the native documentation and the
shipped-file inventory, including support modules not imported explicitly by
the aggregate root. Prefix subject names with `SheafCohomology.`. These
descriptions identify navigation, **not** a claim that every declaration has
the same hypotheses.

| Module | Purpose |
| --- | --- |
| `AcyclicResolution` | Ext/homology comparison from acyclic resolutions |
| `ColimitPostApp` | Evaluation of canonical colimit maps at components |
| `ColimitTransport` | Transport/naturality of canonical colimit comparisons |
| `CompactOpenSections` | Compact-open section and sheafification colimits |
| `DegreeZero` | Degree-zero cohomology and global sections |
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
| `SheafCohomology` | Aggregate root public imports (no new theorem) |
| `SheafCohomologyExamples` | Named private downstream examples using only the root |

## Using the boundary

The checked `SheafCohomologyExamples` target demonstrates the intended imports
for compact-open colimits, quasi-flasqueness, the resolution interfaces, local
cohomology, higher direct images and open base change. Private example names
are not public API. Inspect the sample's actual binders when adapting a result:
the positive/zero-degree split and universe-zero restrictions are essential.
Review actual source hypotheses and typeclass instances rather than guessing
them from the abstract's subject labels. External research records are not
required to build or import this library.
