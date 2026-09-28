# Compact-open sections of native spectral cylinders

Import `SheafCohomology.NativeSpectralCylinderSections` for
`AlgebraicGeometry.SheafedSpace.NativeCylinderLimit.isIso_restrictedGlobalSectionsComparison`.
This is an isomorphism theorem for the *existing* native comparison, not a new
cylinder or limit construction. The ordinary-import example lives in
`SheafCohomologyExamples.NativeSpectralCylinderSections`.

Fix `{ι : Type v} [Preorder ι] [IsDirectedOrder ι]`, `i0 : ι`,
`N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)`, a cone `m : Cone N`
with `hm : IsLimit m`, and `U0 : Opens (N.obj (op i0))`. Its three additional
hypotheses, about the *original* diagram and open, are exactly:

```lean
hstage : ∀ k : ιᵒᵖ,
  SpectralSpace ((N ⋙ SheafedSpace.forget (Type v)).obj k)
htransition : ∀ {k l : ιᵒᵖ} (f : k ⟶ l),
  IsSpectralMap ((N ⋙ SheafedSpace.forget (Type v)).map f)
hU0 : IsCompact (U0 : Set (N.obj (op i0)))
```

The conclusion is
`IsIso (restrictedGlobalSectionsComparison N i0 m hm U0)`.
The map's source is
`colimit ((restricted N i0 U0).rightOp ⋙ SheafedSpace.Γ)` and its target is
`m.pt.presheaf.obj (op (coneOpen N i0 m U0))`. It uses the actual native
`restricted`, `restrictedCone` and `restrictedGlobalSectionsComparison`, with
`hm` referring to the original cone. No spectrality or limit hypothesis for
the restricted diagram, desired isomorphism, surjectivity, nonempty stage/open,
linear order, endpoint, or additive structure is assumed. In particular, `U0`
may be empty: `i0` itself supplies the nonempty directed tail `Set.Ici i0`.

## Proof and ordinary-import client

Public `stageOpen_map` and `stageOpen_base` show that the *literal*
`stageOpen N i0 U0 i` is the inverse image of `U0` along an original
transition. Compactness of a compact-open inverse image under the original
spectral map, and the actual restriction's open embedding, give compactness
of the restricted stage. `isCompact_univ_iff` and the mathlib spectral
open-embedding theorem supply spectrality of that literal stage. For a
restricted arrow, the compact-open **source** inclusion is retrocompact and
spectral (`IsRetrocompact_iff_isSpectralMap_subtypeVal`); compose it with the
original spectral transition. Public `stageMap_fac` identifies that composite
with the restricted map followed by its target inclusion. The published
`SpectralStoneDuality.isSpectralMap_to_subtype_of_comp` transfers spectrality
to the actual restricted arrow without replacing its space or map.

Set `R := restricted N i0 U0` and let `cR` be the forgetful image of
`restrictedCone N i0 m U0`. The inherited `restrictedSpaceIsLimit` supplies
an actual limit for `cR`; the native global-sections theorem then gives
`IsIso (SheafedSpace.nativeGlobalSectionsComparison R cR hcR)` from the
derived spectrality. The imported native-cylinder comparison is opaque.
The proof therefore uses `colimit.hom_ext`, the public coprojection laws
`colimit_ι_restrictedGlobalSectionsComparison` and
`SheafedSpace.colimit_ι_nativeGlobalSectionsComparison`, and
`chosenLimitIso_inv_projection` to identify the *existing* comparison with
native global-sections comparison followed by
`SheafedSpace.Γ.map (chosenLimitIso N i0 m hm U0).inv.op` and
`eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen N i0 m U0))`.
All three factors are isomorphisms. The contravariant `Γ` needs `inv.op`.

The example imports the producer ordinarily and keeps
`originalStage_detects_transported_coprojection` **private**. At any actual
original stage `i : Set.Ici i0`, two sections on `stageOpen N i0 U0 i` with
equal images under the original cone projection *after* the
`coneOpen_eq_stage` inverse-image-open cast have equal images in the
restricted-stage colimit *after* the
`SheafedSpace.restrict_Γ_obj` restriction-object cast. It invokes the
proved isomorphism, `originalStage_restrictedGlobalSectionsComparison`,
and injectivity to cancel the actual comparison. The client does not assume
its desired equality, and does not assert broad eventual equality.

## Reproduce focused checks

From the repository root at the exact code commit, with its unchanged
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json`:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail build +SheafCohomology.NativeSpectralCylinderSections:olean +SheafCohomologyExamples.NativeSpectralCylinderSections:olean
```

The cache fetch must succeed *before* building. In the separate evidence
checkout, the complete actual-origin collector is reproducible by
`lake env lean evidence/native-spectral-cylinder-sections/AuditNativeSpectralCylinderSections.lean`
after those focused checks. This is not a default/full-graph check and does
not substitute for promotion review or the responsible maintainer's decision.
The target pins are Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, published
SpectralStoneDuality `452b7b7be1bea76434cd083b1019a26f96b4ab30`
and published IdealCompletion
`001e3b7508184ecd51e0d86177cb1d54508bf59d`; the entire existing
11-package Lake manifest remains unchanged.

## Attribution and dated lifecycle

The complete original statements and proof expressions come from
`FormalFrontier/incubator` commit
`d8986c460ccae72392ad39550d89669604ec1284`, files
`Incubator/Topology/Sheaves/NativeSpectralCylinderSections.lean` (blob
`62b2c5765ec7d8105d23951baf7f582183fa8455`) and
`IncubatorTest/Topology/Sheaves/NativeSpectralCylinderSections.lean` (blob
`0b52bb4c6dc503204daf53040136538b479f1846`). Only the producer's
comparison import and the client's producer import plus its namespace/end
change in this destination adapter. Reverse those substitutions to recover
both original blobs; SPDX Apache-2.0 and collective Authors notices remain
unchanged. The donor author is worker-b Task
`hive-request-e8a25d6c5328e70c571fe96c3ac0b8102530eaa1` (UID
`ddcebc71-0a10-45a6-b8cf-9606083d850e`). Its fresh independent review
was by worker-a Task `hive-request-39c7e47c551ef244416635d53429219016b1f836`
(UID `1fa3b86b-f473-4750-8009-9c71ad8274be`), at incubator revision
`12f428898f1d962ecbbc4be174d168c608b75629`,
`reviews/native-spectral-cylinder-sections/REVIEW.md`.

Inherited construction and expression credits are distinct from invoked
library results. The comparison and original stage/cast equations are by
worker-b Task `hive-request-f9876d0c2840470583113050ec0546a64eb3954f`
(UID `91e70b6b-63f7-4c56-846f-b66316065a3c`), original revision
`854e446c6b0efbf85c3023e7b21ccd7f9428d8ea`. The cylinder construction
is by worker-a Task `hive-request-153a0400bb1a4285602d24cceb51ae9a56b6b3be`
(UID `38e90320-4a49-4738-9620-3881f7b58af5`), provenance repair by
worker-a Task `hive-request-d984b1de170e87f4be31d9ce565c90299c51e3b3`
(UID `35dd220a-f8a8-4fae-9d05-4a503f2f4b96`), and generic native
restriction by worker-a Task `hive-request-dae0d04e8618b53de43730479c4033d21488695b`
(UID `38967a21-9f85-493d-b98f-67dd712fb00e`), predecessor revision
`800f8c79310c54ade745f79d947f98830272f357`.

The local `tailDirected` expression repeats the parent comparison witness,
ultimately adapted from worker-b Task
`hive-request-065ffb46d5b6d2b9ada197a66b9c1b783b57e00f` (UID
`4720124c-2740-40ba-947d-5be3c681f64e`) at
`FormalFrontier/source-fujiwara-kato-rigid-geometry-i` revision
`e266a5076df34934171cc284ba8f2834e56f8c78`,
`Research/fk-corollary-3-1-12-open-tail-restriction-scratch.lean:27–49`.
The `colimit.hom_ext` expression adapts f987's comparison-leg proof;
the private cancellation expression adapts worker-b Task
`hive-request-4c216dbec01d4be3c9179c965656f0054d638fb8` (UID
`b5bc6fa6-d9ab-4cfa-bd79-3ec1cdf7265a`),
`IncubatorTest/Topology/Sheaves/NativeLimitGlobalSections.lean`, and
f987's comparison client. The *invoked* native Gamma theorem comes from
4c216, with published SheafCohomology precursor
`32b1fb7787d5036c8b7181565a22a460b160f91d`.
Official native construction credits worker-a Task
`hive-request-700e4f0e3debb32b4538a1158e70ca099e66c254` (UID
`02943c65-933d-4b1e-974b-decbd5d5f153`); official limit preservation
credits worker-b Task `hive-request-502206a7e28d7384c6a1ab57a9acf7a38c6a9eb4`.
The published SpectralStoneDuality Subspace criterion is **invoked**, not
copied, and mathlib supplies spectral, retrocompact and open-embedding facts.
No private source text or source-specific coverage claim enters this library.

At donor author-time its parent was unaccepted, as described in its
then-current guide. Anchor later accepted that exact parent as an
unregistered comparison leaf at incubator issue #4/comment 54410, and
accepted the exact spectral donor **unregistered only** at #4/comment
54519 after review and separate donor evidence at
`0d9aaf99312a03c4833730913275394932f6c734`. Neither event accepts
this destination adapter. It was authored by worker-a Task
`hive-request-5d68fce000ac813d7755bf44f7aa4a699799d102` (UID
`e4c4c56a-25fc-4725-9cd3-4061a5326fbc`) from the **then-unaccepted**
target `FormalFrontier/sheaf-cohomology` revision
`d443e034746972593ec0c91f64268771a3013b5a` (PR #129), with
explicit rework if that target's interfaces changed. At that adapter snapshot,
its new code was **unreviewed and unaccepted**, without root/default-target
registration, PR, merge or release. The later source-only 81-module assembly
at 2026-09-27 20:41:17 UTC registered both leaves, preserving their exact
statements, proof expressions and the eleven-package graph. Scoped independent
review `f603c82f5ce9fc81f1f5efa8ad4db847faf557cf` subsequently approved
the mathematical/API/provenance/registration increment. Full 81-module CI610
on `a67d8f00d6da10ccd6af1beebe04be053fcdc1cd` succeeded at 22:04:27 UTC;
the owner inspected its complete both-target build and private-inclusive
standard-axiom evidence, not just the eight focused leaf origins.

The corrected 79-module predecessor later completed its own final review,
CI643, owner decisions and protected integration; its official GitHub release
`ca6684a3b2eaa21a9e415175ceda61d9a4ac75c8` was verified on 2026-09-28
at 00:28:20 UTC. Its documentation-only 81-module successor normally merged
that accepted main `f950b52d57e87efb70f4c8adb6d84856248520e9`, keeping
all 81 Lean blobs, both roots, eleven package objects and CI inputs fixed.
Full CI648 on corrected `6e055c187a6e097636f2e9b5bf5d4f5eba351876` succeeded
on 2026-09-28 at 01:05:13 UTC. The owner consumed the complete both-target
build and all 81-module/private-inclusive standard-axiom evidence. Following
fresh final review `3f39164f7f7fd6b65737106abf6ad22a1648a38f` and separate
main/prep/public decisions and protected integration, official private GitHub
release `b743039857ca8c206b6a8cdb99afe7c7e8ce0c25` was verified at 02:39:17 UTC.
These are the 81 contribution's own completed gates, not acceptance of a later
additive or generic successor. The additive global-section contribution received
its own subsequent full CI666, final review and owner decisions: accepted 83
main `9ba31ec9d399343a81e7284f7856f53c6a1d7f5c` and official private
release `6793f2ff8469d1cab23a98ac2da22a3286d22f8e`, verified on
2026-09-28. The following 84 generic-restriction successor was unaccepted
at that earlier reconciliation. It subsequently passed changed-input CI674
and independent final review and was accepted at main/release-prep
`36e49294f84208fa678872e84b6bdbd96c603188`, then published as official
private `e5d7d6e60243da2ec9a2af243fac3f3a3bf7dc37` (issue #34/comment
56186). This still **unaccepted 85** successor does not change this Type-only
spectral-cylinder body or establish an additive compact-cylinder theorem.
No source correspondence, source coverage or incubator conversion follows.
