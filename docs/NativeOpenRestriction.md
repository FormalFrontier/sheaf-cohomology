# Native restriction to inverse-image opens

Import `SheafCohomology.NativeOpenRestriction` for the public API in
`AlgebraicGeometry.SheafedSpace`. Its coefficient category is
`{C : Type (v + 1)} [Category.{v} C]`, and its objects are
`SheafedSpace.{v + 1, v, v} C`. The base-space and coefficient category use the
same universe `v`. There is no requirement of points, a nonempty space or open,
extra limits, or a concrete coefficient category. Setting `C = Type v` gives
the **same** declarations as the original Type-valued API, with no renaming or
parallel implementation. The existing ordinary-import Type example
`SheafCohomologyExamples.NativeOpenRestriction` remains unchanged;
`C = AddCommGrpCat.{v}` is another specialization.

Given `g : X ⟶ Y` and `V : Opens Y`, define the source open *exactly* by
`U := (Opens.map g.hom.base).obj V`. The native arrow
`restrictOnPreimage g V` has type

```lean
X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding
```

It is induced by mathlib's `PresheafedSpace.IsOpenImmersion.lift` of the
**existing** open immersion `Y.ofRestrict V.isOpenEmbedding` along
`X.ofRestrict U.isOpenEmbedding ≫ g`, not by constructing a second sheaf or
base-change map. `restrictOnPreimage_range` supplies the inverse-image range
witness. `restrictOnPreimage_fac` states the commuting inclusion square as an
equality of **full sheafed-space arrows**, and `restrictOnPreimage_unique`
characterizes the arrow by that same full-arrow square via the open-immersion
`lift_uniq`. `restrictOnPreimage_base` identifies its literal underlying
continuous map with the official
`TopCat.Sheaf.OpenBaseChange.preimageMap g.hom.base V`.

For an independently named `U' : Opens X` and proof
`h : U' = (Opens.map g.hom.base).obj V`, use
`restrictOnNamedPreimage g V U' h`. Its inclusion square
`restrictOnNamedPreimage_fac` uses that equality rather than treating the
opens as definitionally equal. `restrictOnNamedPreimage_id` proves identity
after the `Opens.map_id_obj` cast; `restrictOnPreimage_comp` proves composition
after the `Opens.map_comp_obj` cast, using the monic *native restriction*
inclusions. The composition source is `(Opens.map (f ≫ g).hom.base).obj W`,
transported to the iterated inverse image
`(Opens.map f.hom.base).obj ((Opens.map g.hom.base).obj W)`.

`restrict_Γ_obj X U` identifies global sections of the native restriction
with `X.presheaf.obj (op U)` using `Opens.isOpenEmbedding_obj_top`.
`ofRestrict_c_app_self` identifies the inclusion's component on that open.
With **both** explicit `eqToHom` transports, `restrictOnPreimage_Γ_map`
identifies `Γ.map (restrictOnPreimage g V).op` with the original component
`g.hom.c.app (op V)`. `restrictOnNamedPreimage_Γ_map` also transports from
the canonical inverse-image open to `U'`, using `h.symm` in the
presheaf-object cast. The proof uses the full-arrow square, the actual
presheaf morphism's naturality and cancellation of an equality transport:
`TopCat.Presheaf.pushforward C` maps an `eqToHom` to an isomorphism, hence a
monomorphism for arbitrary `C`. It uses no Type-element injectivity or
assumed component equality.

The existing ordinary-import **Type** example composes two genuine native
arrows and recovers the original composite component with its nondefinitional
`Opens.map_comp_obj` cast. The separate ordinary-import **additive** example
`SheafCohomologyExamples.NativeOpenRestrictionAdditive` checks the same
readback for composable `AddCommGrpCat` arrows. Its *named private* theorem
`composed_sections_readback` retains the explicit cast and proof; it neither
creates a public theorem nor assumes its desired equality. The additive
example is registered in the `SheafCohomologyExamples` aggregate and its
default target by this source-only 84-module assembly. The public root already
imports the same generalized producer; it needs no new producer import.

## Boundaries and verification

This API does **not** construct principal-tail functors, restricted cylinder
cones or limits, native-limit comparisons, colimit-leg naturality, spectral
transport or the additive compact-cylinder endpoint. Preservation of a limit
by coefficient forgetting does not imply reflection of an additive limit.
No source-level correspondence or coverage decision follows from this unit.

The accepted **unregistered incubator donor** is
`ae8d32640fc9c946778fdd79fbc37528b433fa06` (tree
`708303c23bfa555580d8768661635bf5875eeb1e`), accepted only as a leaf
in incubator issue #4 comment 55201 after the full independent review in
comment 55191. Its original focused nine-target build and audit, recorded at
`a33932b120b489e150af2da9994cf1a7d8410e57`, checked 92 declarations
from **eight unchanged generating modules**, including private/generated
declarations. The then-anonymous additive example contributed **zero retained
origins** to that audit. The separate repaired-client build and evidence at
`8585432834789145f2ac647327d47749332bacf0` checked the subsequently
named **private** `composed_sections_readback`: one retained declaration with
only `propext`, `Classical.choice` and `Quot.sound` in its complete transitive
axiom closure. The original nonpasses were an unsupported `-j` option, a
composition-associativity mismatch repaired before the original successful
build, and an audit attempt expecting an origin from an anonymous private
example. They remain recorded in the donor evidence; the named-proof repair
had no Lean/build/audit nonpass and is not a retroactive pass or an
invented combined 93-origin run. These are **donor** checks, not destination
build or axiom evidence.

The original Type destination handoff targeted a then-unaccepted 73-module
candidate. Its corrected successor was accepted and released as official
`6aa8528f28264d9b44de0f31e72696d8d95ce97d` on 2026-09-27 at 21:19:58 UTC.
The 75-module reconciliation carried both transferred Type Lean blobs; full
CI621 on `efcfeae07fa909b9c1d20bdd665cf733eb11cb4d` succeeded at
22:20:06 UTC. After owner intake, independent final review and separate
protected decisions, the official 75 release
`57decc6d5106fe32dc57f9684de38f6e10534de5` was verified at 22:30:32 UTC.

The later generic three-path transfer targeted the frozen, **then-unaccepted**
destination **83** base
`70d1aad387e72104ae294ac07a32c113d7f72e75` (tree
`09c148c9c8079e8b7f812e3ced72b113afce36b4`), not the then-published
75 release or protected `main`. The original destination 83 CI result did not
certify this changed graph: the generalized producer affects twelve existing
modules by source import (the OpenRestriction, CylinderLimit,
CylinderComparison and SpectralCylinderSections producer/client pairs, both
aggregate roots, and the two examples importing the public root), plus the new additive
client. **No destination build or axiom audit was run for this static transfer.**
Anchor's subsequent source-only registration preserves both transferred Lean
blobs and the original Type client, adding only the new example-root import,
API navigation, metadata and credit. At its 2026-09-27 23:04 UTC assembly,
no destination build/axiom pass or independent destination approval was claimed.
Full CI627 on the old 83-module parent succeeded at 22:47:17 UTC, but did not
validate these changed inputs. The original 84 candidate
`53a0a858ec7d3fab15c96f9f10ba8c31d8e21554` later passed full both-target,
private-inclusive CI637 at 23:36:49 UTC (issue #34, comment 55462); the
separate scoped destination review
`efecfe1af9a07f376fd2c92e7f59125ac14ddb3c`/native4379 covers the original
registration, not this changed-header, merged-ancestry successor. The 77/79/81/83 predecessor gates
that were open at assembly are now complete. Actual accepted 83 main/release-prep
`9ba31ec9d399343a81e7284f7856f53c6a1d7f5c` was published as official
private GitHub `6793f2ff8469d1cab23a98ac2da22a3286d22f8e` on 2026-09-28,
with verified preceding 81 release
`b743039857ca8c206b6a8cdb99afe7c7e8ce0c25` as sole public parent.
This 84 successor inherits its accepted 83 additive-credit headers unchanged;
its generic producer and additive client now have reversible collective-credit
header repairs. All module-onward bytes remain from the original 84 candidate.
Original CI637 does **not** certify those changed headers. Applicable full
successor build/private-inclusive standard-axiom CI and a fresh independent
final main/prep/public review still precede separate owner acceptance, protected
integration and verified publication. This 84 successor remains **unaccepted**;
donor acceptance is not destination integration or incubator conversion.

## Provenance

Original Type producer/client: Formal Frontier worker-a Hive Task
`hive-request-dae0d04e8618b53de43730479c4033d21488695b`, UID
`38967a21-9f85-493d-b98f-67dd712fb00e`. Earlier Type destination adapter:
worker-a Task `hive-request-5de3ebfab00e632e44a5c020cb1fd800467bc20f`,
UID `ac4b4dd0-3208-40c0-9352-a602f551452a`. Generic producer and close
adaptation of the Type client to additive coefficients: worker-a Task
`hive-request-30271b71e726fc52aa0a7c7670ba0eca5de6eaac`, UID
`295217cc-fb36-46be-968d-03070242fd2b`. Additive header and named-private
auditability repair (not mathematical authorship): worker-a Task
`hive-request-97bfa2a350ebf1a403402c688ba8f4c80ca4a394`, UID
`79c83628-cbc1-4702-a72f-ea4c3412c00d`. Route analysis, not proof:
worker-b Task `hive-request-95f10ba06d205ac6940b05ee7c67b16ff0e0f725`,
UID `df7518ed-d71a-4cb1-b4ab-d6810ad3a1ad`. Full donor independent review:
worker-b Task `hive-request-f06218b26e9e91423ccc33d15127fec071e2e862`,
UID `3d93f379-6d25-4640-9585-58a1ad623e32`, at report
`9ce66df6fc29d6386ce9b5d72ca7f9b3bc2bb90e`.

Only this exact three-path static transfer and guide are by worker-a Task
`hive-request-b45999b6c3820ed16f789cbb8a9b68ce126bf8f6`, UID
`7e0cdddd-188a-4d9e-807b-1f46e1fb6915`; they do not constitute a new
mathematical contribution or an acceptance review. The lift, its factorization
and uniqueness are reused from Andrew Yang's Apache-2.0 mathlib
`Mathlib/Geometry/RingedSpace/OpenImmersion.lean`. Mathlib supplies native
restriction and `Γ`; the Apache-2.0 official
`SheafCohomology/OpenBaseChange.lean` (Formal Frontier Agents) supplies the
`preimageMap` expression. Both producer and additive client retain their
original SPDX, Generality and provenance/auditability notices. Their original
author text and continuation lines now follow `Contributor:` beneath
`Authors: Formal Frontier Agents`; reversing just this header change recovers
each complete frozen 84 file. The Type client remains byte-identical. No
incubator dependency, source-local experiment or private source asset was
copied. Source coverage is a separate decision.
