# Additive sections of a native compact-open cylinder

Import `SheafCohomology.NativeAdditiveCylinderSections` to use the
actual-cone comparison. Fix a directed preorder `ι : Type v`,
`S : ιᵒᵖ ⥤ SheafedSpace.{v+1,v,v} AddCommGrpCat.{v}`, an index `i0 : ι`,
an **arbitrary** original native cone `m : Cone S`, and an open
`U0 : Opens (S.obj (op i0))`. The comparison definition and both
projection laws need only `[Preorder ι]`; directedness is used for the
IsIso theorem, not smuggled into the ordinary colimit construction.
Write
`R := NativeCylinderLimit.restricted S i0 U0` and
`mR := NativeCylinderLimit.restrictedCone S i0 m U0`.

`NativeCylinderLimit.nativeAdditiveCylinderSectionsComparison S i0 m U0`
is an additive morphism

```lean
colimit (R.rightOp ⋙ SheafedSpace.Γ) ⟶
  m.pt.presheaf.obj (op (NativeCylinderLimit.coneOpen S i0 m U0))
```

for **any** `m`; no `IsLimit`, spectral, compactness, surjectivity or
nonempty-space assumption enters its definition or its arrow laws. The
codomain is sections of the **original** cone point over the inverse image
of `U0` under the original projection at `i0`, not sections of a chosen
replacement limit. The comparison first uses the accepted **donor**
`SheafedSpace.nativeAdditiveGlobalSectionsComparison R mR` on the actual
restricted diagram and cone, then the *forward* transport
`eqToHom (SheafedSpace.restrict_Γ_obj m.pt (coneOpen S i0 m U0))` from
global sections of the literal restricted cone point to the original open.
`mR.pt` is literally the restriction of `m.pt` to that open.

The restricted coprojection law
`NativeCylinderLimit.colimit_ι_nativeAdditiveCylinderSectionsComparison`
identifies each colimit leg followed by the comparison with the actual
`Γ.map (mR.π.app (op i)).op` followed by that forward transport. The
**original-stage** law
`NativeCylinderLimit.originalStage_nativeAdditiveCylinderSectionsComparison`
is an equality of `AddCommGrpCat` morphisms, not merely carrier functions:

```lean
eqToHom (SheafedSpace.restrict_Γ_obj
    (S.obj (op i.1)) (stageOpen S i0 U0 i)).symm ≫
  colimit.ι (R.rightOp ⋙ SheafedSpace.Γ) i ≫
    nativeAdditiveCylinderSectionsComparison S i0 m U0 =
  (m.π.app (op i.1)).hom.c.app (op (stageOpen S i0 U0 i)) ≫
    eqToHom (congrArg (fun W : Opens m.pt => m.pt.presheaf.obj (op W))
      (coneOpen_eq_stage S i0 m U0 i).symm)
```

The left `.symm` moves original stage-open sections into Γ of the
**literal** restricted stage. The right `.symm` moves the projection's
preimage-open sections back to sections on the named `coneOpen` in `m.pt`.
The proof applies the generic `restrictOnNamedPreimage_Γ_map` to the
actual original projection and identifies the native cone component by
its monic open-inclusion square. It does not use an assumed Γ-forgetting
bridge, a chosen-limit comparison, or a carrier-only equality.

If `hm : IsLimit m`, every original stage of
`S ⋙ SheafedSpace.forget AddCommGrpCat.{v}` is spectral, every original
transition is spectral, and `U0` is compact (including the empty open),
`NativeCylinderLimit.isIso_nativeAdditiveCylinderSectionsComparison`
proves this comparison is an isomorphism. The generic
principal-tail filteredness needed **only inside this proof** is supplied
locally: `i0` inhabits the tail, `tailDirectedOrder i0` supplies
directedness, and mathlib infers `IsFiltered (Set.Ici i0)`.
No global tail instance or linear order is added. The generic
`restrictedIsLimit S i0 m hm U0` **constructs** the required native
restricted-cone limit. The separate reusable generic module
`SheafCohomology.NativeSpectralCylinder` proves spectrality
of the actual restricted stages and maps for any coefficient category
`C : Type (v+1)` with `[Category.{v} C]`, directly from the original
spectral system and compact `U0`, with *no cone or limit assumptions*.
Its topology proof occurs only once: `spectralStage` transports compactness
along original transitions and uses the compact-open embedding;
`spectralStageMap` uses retrocompactness of the original open, the actual
native `stageMap_fac` square and the published spectral-subspace criterion.
The accepted **donor** additive global comparison applies to the constructed
restricted limit and these spectral hypotheses. Composing its isomorphism
with the forward `eqToHom` proves the endpoint without assuming the result.
The original Type-valued chosen-limit endpoint still uses this shared
helper at `C := Type v`, with its original public conclusion unchanged.

An ordinary importer,
`SheafCohomologyExamples.NativeAdditiveCylinderSections`, contains
the **named private**
`originalStage_detects_transported_coprojection_additive`: equality of
two sections under the *actual original projection* and the right-hand
named-open cast implies equality after the left-hand restriction-object
transport and actual colimit coprojection. It uses this proved `IsIso`,
`forget AddCommGrpCat` and concrete injectivity, and the original-stage
arrow law. Neither desired equality nor injectivity is assumed. Empty
opens and spaces are not excluded. The client is a usage check, not a
source-correspondence claim.

## Provenance and state

**Donor chronology:** At author-time, the incubator successor
`6ceec6dbfcfca0cad053e291457c8587c60839c5` (tree
`1e9e6ca983535ff2c8f658d0bde8994ce6f7aaca`) was unaccepted and
unregistered. Its sole accepted, unregistered parent was
`3f42acfa49bc773a4b12727e5f1b68b7299680a7` (tree
`2fb2790a77f9518618a15ffed122fb0d9e1c6c45`, #4/55575). Independent
review `dd535468fc9a4d14ec2ac90e794e41604ddcba4c`,
`reviews/native-additive-cylinder-sections/REVIEW.md`, was favorable with
an evidence-wording qualification. Anchor subsequently accepted **only the
unregistered incubator leaf** at #4/55732 after complete evidence intake;
this does not accept its destination adapter. The earlier accepted but
**unregistered** leaves include generic restriction
`ae8d32640fc9c946778fdd79fbc37528b433fa06` (#4/55201), actual
additive global sections `4806e203844ff4f4abbcf06d35a93b25a5fbf814`
(#4/54912), Type spectral endpoint
`d8986c460ccae72392ad39550d89669604ec1284` (#4/54519), and the
generic cylinder `3f42acfa` above, reviewed mathematically/API at
`de388e4a01404d58c3afcd9306cb990138ce9f0a` and for documentation
at `7daf6056828d4231167cd3fa393b5f5823d34519`. The historical
owner clarification #4/55599 corrects a source-only planner parenthetical:
the accepted global *comparison/leg* need no filteredness, whereas its
IsIso endpoint does. The present definition/arrow laws reflect that
separation. The historical
Type-cylinder provenance objection `234e1ae9448fd3eec5bd4250260d9331ebfe8f9a`
and separately reviewed repair `85aeeef35c3b3f0f01d56869b448a4f49e05f5b5`
remain credited in `docs/NativeCylinderLimit.md`; those reviews do
**not** review the additive donor. The original Type spectral commit
`d8986c460ccae72392ad39550d89669604ec1284` remains historically
unchanged, but the **current** Type spectral module is modified by this
generic-helper extraction. Only the donor's final2 changed-input
ten-target build and private-inclusive audit cover that module at `6ceec`;
old Type evidence alone does not. No donor evidence certifies this
destination graph or establishes source correspondence, coverage or a
converse.

The present additive comparison, two laws, IsIso proof, one-time generic
extraction, tail alias and private additive client are by worker-b Hive Task
`hive-request-581a9584fa061c70e8f8581b23cc51bae1d3f5bf`, UID
`0eb3d3fc-0bb3-4098-ab2f-892fe8a763f4`. **The extracted topology proof
expression belongs to the original Type spectral author** worker-b Task
`hive-request-e8a25d6c5328e70c571fe96c3ac0b8102530eaa1`, UID
`ddcebc71-0a10-45a6-b8cf-9606083d850e`, and is not newly invented
by this extractor. The Type chosen-limit comparison/stage-cast expression
belongs to worker-b Task
`hive-request-f9876d0c2840470583113050ec0546a64eb3954f`, UID
`91e70b6b-63f7-4c56-846f-b66316065a3c`. The generic cylinder and
existing additive restricted-limit client belong to worker-a Task
`hive-request-27d70680c0e69c147294098e3ac13b1c7092c0e1`, UID
`bfe6acf9-1385-4602-a9b8-1e88f6908b1a`; the original Type cylinder
belongs to worker-a Task
`hive-request-153a0400bb1a4285602d24cceb51ae9a56b6b3be`, UID
`38e90320-4a49-4738-9620-3881f7b58af5`; its independent provenance
repair belongs to worker-a Task
`hive-request-d984b1de170e87f4be31d9ce565c90299c51e3b3`, UID
`35dd220a-f8a8-4fae-9d05-4a503f2f4b96`.

The original directed-tail expression is adapted from worker-b Task
`hive-request-065ffb46d5b6d2b9ada197a66b9c1b783b57e00f`, UID
`4720124c-2740-40ba-947d-5be3c681f64e`; the generic restriction
author is worker-a Task `hive-request-30271b71e726fc52aa0a7c7670ba0eca5de6eaac`,
UID `295217cc-fb36-46be-968d-03070242fd2b`, with repair/client by
worker-a Task `hive-request-97bfa2a350ebf1a403402c688ba8f4c80ca4a394`,
UID `79c83628-cbc1-4702-a72f-ea4c3412c00d`, and initial restriction
author worker-a Task `hive-request-dae0d04e8618b53de43730479c4033d21488695b`,
UID `38967a21-9f85-493d-b98f-67dd712fb00e`. The unchanged
accepted **donor** additive-global producer/ordinary client are by worker-a Task
`hive-request-0b67e8c17f9041202a7550e7a7703f53d6bb4004`, UID
`7b289efe-e184-4c33-9723-7ef39e977b59`; their private Γ bridge is
not copied. Route analyst worker-b Task
`hive-request-95f10ba06d205ac6940b05ee7c67b16ff0e0f725`, UID
`df7518ed-d71a-4cb1-b4ab-d6810ad3a1ad`, and source-only planner
worker-b Task `hive-request-a6e53b1efbd7897c57748cf5757c7851e09abbc6`,
UID `d47064ce-24b7-4688-a572-8b75c1406b2e`, provided plans, **not proofs**.
See the three prior guides for further unchanged expression-level credit.

Mathlib's coefficient-generic open-immersion lift is due to Andrew Yang;
mathlib also supplies spectral, constructible, retrocompact and filtered
category facts. The spectral subspace criterion is invoked, not copied,
from published `SpectralStoneDuality.Subspace` release
`452b7b7be1bea76434cd083b1019a26f96b4ab30`; the published
SheafCohomology native-limit/Γ and additive forgetting precursors are at
`32b1fb7787d5036c8b7181565a22a460b160f91d`; official
IdealCompletion release `001e3b7508184ecd51e0d86177cb1d54508bf59d`
is a fixed existing dependency. Destination pins are Lean
`leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, SpectralStoneDuality
`452b7b7be1bea76434cd083b1019a26f96b4ab30` and IdealCompletion
`001e3b7508184ecd51e0d86177cb1d54508bf59d`; the entire existing
**eleven-package destination** manifest is unchanged. The donor's
twenty-package manifest and incubator/Sheaf self-dependency are not copied;
no source assets are copied.

## Destination adapter and reproduction

This section records the **historical static, unreviewed and unregistered**
destination adapter snapshot before the source-only registration. It starts
from frozen **unaccepted** parent
`651f8223c7dbb2df870f3f594077365bf6767d7f`, tree
`7f69109ef07c5261c9f5b3d2ccf3163e56a6055d` (Sheaf Cohomology #34).
All three new Lean files replace only their `Incubator.Topology.Sheaves.`
import prefix with `SheafCohomology.`, add `Authors: Formal Frontier Agents`
and retain the donor's exact worker-b Task/UID on a separate `Contributor`
line. The helper also keeps its original topology-expression credit. The
new client alone replaces namespace/end
`IncubatorTest.NativeAdditiveCylinderSections` with
`SheafCohomologyExamples.NativeAdditiveCylinderSections`. The two modified
producers differ from the donor only by the import prefix. These controlled
edits are reversible; no theorem, proof, option, import kind or mathematical
namespace changes. The separate preexisting
`SheafCohomologyExamples.NativeCylinderLimitAdditive` collective-credit
repair is untouched.

Prior destination Type-spectral adaptation is by worker-a Task
`hive-request-5d68fce000ac813d7755bf44f7aa4a699799d102`, UID
`e4c4c56a-25fc-4725-9cd3-4061a5326fbc`; generic-cylinder transfer is
by worker-a Task `hive-request-174ca2aad0df7bdc9275c6af83be955de855bd97`,
UID `abffae59-12f3-4536-8643-d91504fc806d`, and its earlier root
registration by worker-a Task
`hive-request-f2b4090a882686df924af77bc982594879d2f8a3`, UID
`bd0b26e2-40ab-4ab0-b12f-60aaf5f4e356`. This static adaptation and
guide are by worker-a Task
`hive-request-9dcde8f6d7062e56cb44b8468857f81145d25e0f`, UID
`8c900d59-2daf-4646-af0c-9df846d22539`, **not** the author of the
donor mathematics. The exact code head and provider-readback table are
retained at Sheaf Cohomology #34, not inferred from this guide.

The subsequent 2026-09-28 source-only registration adds two public producer
imports and one ordinary named-private-client import, then updates navigation,
credit and scope metadata; the five donor-derived Lean payloads and all 86
nonroot Lean blobs remain unchanged. This registration is by worker-a Task
`hive-request-b43835c27fa736b37edbf2bf908b44a6e81e0f4e`, UID
`badc1bbb-885f-4d3a-9dcd-2ddc478616a5`, not a proof author. The 88-file
static import traversal has 55 producer leaves, 31 client leaves (28 private,
three named-public) and two roots, with 14 destination modules in the changed
reverse dependency closure. At the 2026-09-28 02:31 UTC owner checkpoint,
actual 79 was released; final 81 CI648 was owner-intaken but not accepted or
released, and 85 CI655 was successful for metadata only without owner intake.
Neither donor nor predecessor evidence establishes the changed destination
88-graph build or complete private-inclusive standard-axiom pass. Actual-parent
and lifecycle rework after ordered 81→83→84→85 releases is expected.

For a later **authorized** computation at the exact destination revision,
install its toolchain, fetch the matching mathlib cache *before* building,
then check the relevant modules (documented but **not executed** here):

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
env LEAN_NUM_THREADS=2 lake --wfail build +SheafCohomology.NativeSpectralCylinder:olean +SheafCohomology.NativeAdditiveCylinderSections:olean +SheafCohomology.NativeSpectralCylinderSections:olean +SheafCohomologyExamples.NativeAdditiveCylinderSections:olean
```

That focused command alone would not certify the whole 88-module graph or
its transitive axioms, and no destination computation is claimed here.
At that 02:31 UTC checkpoint Anchor still had to reconcile ordered
81→83→84→85 actual-parent releases, obtain complete destination evidence and
fresh independent review, and decide acceptance and individual publication.
That original snapshot does not change protected refs, register the incubator
leaf or decide source coverage.

## Later actual-parent and evidence lifecycle (2026-09-28)

Actual81/83/84 completed separate official private releases at
`b743039857ca8c206b6a8cdb99afe7c7e8ce0c25`,
`6793f2ff8469d1cab23a98ac2da22a3286d22f8e` and
`e5d7d6e60243da2ec9a2af243fac3f3a3bf7dc37`. Separately, original frozen88
PR142 head `1ded7c974bdb6cd753e393fbc8d09bb2782c69e9` passed
full both-target/private-inclusive CI665/UI63/artifact121236 at
2026-09-28 04:57:52 UTC, before the actual83/84 releases; that evidence was
owner-intaken at issue #34/comment 55987. Independent mathematical/API/provenance/
registration review `eed9f975efd4dd17cbace2d3a40d4d041319b67f`
(native4411) was owner-intaken #34/55894. These are complete scoped results,
not missing review or a metadata-only check; neither accepts the successor.
Actual85 subsequently passed full CI685/artifact131785, independent
consolidated review `fc9bb966ca2c9f9426fd817341f787e851351bcd`
(native4442–4444) and individual owner gates: accepted main/release-prep
`25e596baca25cf582aa2f6d9ba22d7833de74ec7`, official private release
`2c7b5e3e2e94704b9aa825c1aed88a880cf78dae` (#34/56450).

This still **unaccepted 88** actual-parent successor normally merges accepted
85 development into frozen88 registration. Its two modified producers,
three new Lean modules, aggregate roots and proof bodies stay frozen88-exact;
thirteen inherited files adopt accepted85's complete collective-credit
headers, retaining original Contributor/Task/UID and every module-onward
byte. Frozen88 CI665 and actual85 CI685 do not certify the changed header
inputs. Anchor must arrange applicable full both-target/private-inclusive
successor88 CI, fresh author-distinct consolidated final main/prep/public
review and separate owner gates before actual private publication. This static
lifecycle reconciliation is by worker-a Task
`hive-request-00a2d16de3e9d91c3ab18427527337bc2da95a50`
(UID `c0b22631-f9c1-4763-a28d-e32889a3e05f`), not an author of the
topology, generic or additive proofs, original adapter or root registration.
No release, source-coverage or incubator-conversion claim follows.
