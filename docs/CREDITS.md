<!-- SPDX-License-Identifier: Apache-2.0 -->

# Credits and provenance

**Formal Frontier Agents** is the collective author credit for this library's
original Lean development, examples and explanatory documentation. Anchor
coordinated its maintenance; other project contributors and independent
reviewers, including Beacon, Lattice and Atlas, are credited in the published
repository history and applicable individual Lean contributor notices.
The project uses AI agents for formalization, adaptation, documentation and
independent agent review. Neither that review nor collective credit asserts
human peer review, copyright ownership or source-author endorsement.

The mathematical arguments use Lean and mathlib's native sheaf, limit,
sheafification, stalk, Ext and derived-functor infrastructure. In particular,
**Andrew Yang's 2025 Apache-2.0 mathlib open-immersion construction** in
`Mathlib/Geometry/RingedSpace/OpenImmersion.lean` supplies the lift,
factorization and uniqueness adapted for the native open-restriction API;
mathlib's terms and original contributor credit remain applicable. The
project's native `OpenBaseChange` results provide the related `preimageMap`
expression. The [native restriction guide](NativeOpenRestriction.md) explains
the actual arrow and section-component equations.

The library's coefficient-forgetting comparisons adapt additive constructions
to commutative-ring coefficients with the differences in colimit and pullback
hypotheses stated in the [ring guide](CommRingForget.md). The
[ring global-section](NativeCommRingGlobalSections.md) and
[original-open ring-cylinder](NativeCommRingCylinderSections.md) constructions
build on their additive and generic-cylinder counterparts; the
[open-naturality](NativeCylinderOpenNaturality.md) and
[tail-change](NativeCylinderTailChange.md) guides describe their shared
category-generic interfaces. Adaptation and registration do not replace the
original authorship of imported mathematical arguments, nor turn conditional
statements into unconditional ones. Preserved individual credit and review
provenance remains in repository history and the original headers of shipped
Lean files; this guide is not a runtime task ledger.

For background in compact-open and quasi-flasque methods see Kazuhiro Fujiwara
and Fumiharu Kato, *Foundations of Rigid Geometry I*,
[arXiv:1308.4734v5](https://arxiv.org/abs/1308.4734v5). A mathematical citation
is not a claim of approval by these authors or of complete source coverage.
No source PDF or substantial excerpt is bundled.

Original project contributions use the [Apache-2.0 license](../LICENSE),
without asserting a new copyright holder or relicensing third-party work.
Authentic upstream terms and notices continue to apply. The
[README](../README.md) gives user-facing scope and reproduction guidance;
`formalization.yaml` supplies concise candidate metadata rather than a
revision-by-revision review or publication history.
