# Native limits of principal-tail open cylinders

Import `SheafCohomology.NativeCylinderLimit` for the API in
`AlgebraicGeometry.SheafedSpace.NativeCylinderLimit`. The separate
`SheafCohomologyExamples.NativeCylinderLimit` (Type-valued) and
`SheafCohomologyExamples.NativeCylinderLimitAdditive` (additive-valued) are
ordinary-import clients. None imports the incubator or a source-research
repository.

Let `ι : Type v` be a preorder with `IsDirectedOrder ι`, let `i0 : ι` be an
**explicit** distinguished index, and let `C : Type (v + 1)` carry
`[Category.{v} C]`, inferred from
`N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} C`. Given a native cone
`m : Cone N`, its native limit witness `hm : IsLimit m`, and an arbitrary
`U0 : Opens (N.obj (op i0))`, the principal construction is

```lean
restrictedIsLimit N i0 m hm U0 :
  IsLimit (restrictedCone N i0 m U0)
```

Here `restricted N i0 U0` is the actual functor of **native sheafed-space
restrictions** over `(Set.Ici i0)ᵒᵖ`; `restrictedCone N i0 m U0` is its
canonical cone, with point literally
`m.pt.restrict (coneOpen N i0 m U0).isOpenEmbedding`. No limit of the
restricted diagram is assumed. There is no linear-order hypothesis, nor any
nonempty-space or nonempty-open hypothesis.

## Constructions and use

- `tailInclusion i0 : Set.Ici i0 ⥤ ι` is final by directedness, and
  `tailInclusion_op_initial` makes its opposite initial. `tailDiagram N i0`
  restricts the original diagram to this opposite tail.
- `transition N i0 i` maps tail stage `i` to the distinguished stage;
  `stageOpen N i0 U0 i` is the inverse image of `U0` under this transition.
  `stageOpen_map` supplies the equality of named inverse-image opens needed
  for each arrow `stageMap N i0 U0 f`. `restricted N i0 U0` comprises these
  literal restrictions and native arrows. `inclusion N i0 U0` is their
  natural transformation to the original tail diagram.
- `coneOpen N i0 m U0` pulls `U0` back along the actual projection at `i0`.
  `coneOpen_eq_stage` identifies it with the inverse image of each stage
  open; `stageOpen_base` identifies the distinguished-stage open with `U0`.
  `coneComponent` uses the named-preimage native restriction arrow, and
  `coneComponent_fac` records its commuting native inclusion square. The
  private naturality helper proves full native-arrow cone naturality.
- `tailIsLimit N i0 m hm` transfers the original limit along the initial
  opposite tail. For any `t : Cone (restricted N i0 U0)`, the arrow
  `originalLift N i0 m hm U0 t : t.pt ⟶ m.pt` satisfies
  `originalLift_fac`; `originalLift_range` proves it lands in `coneOpen`,
  even for empty spaces and opens. `restrictedLift` factors that arrow through
  the actual native open restriction, with `restrictedLift_fac` and
  `restrictedLift_component` establishing the native cone equations. Monic
  cancellation proves uniqueness in `restrictedIsLimit`. No preservation of
  native limits by the underlying topological-space functor is asserted.

The private theorem `lift_original_projection` in the ordinary-import client
`SheafCohomologyExamples.NativeCylinderLimit` specializes to `C = Type v`,
takes *any* `t : Cone (restricted N i0 U0)` and any tail stage
`i : Set.Ici i0`, applies `(restrictedIsLimit N i0 m hm U0).lift t`, and
recovers its original-projection equation after composing with the native
restriction inclusion. It neither posits the desired restricted `IsLimit`
nor replaces the diagram with an alternate model.

The separate private theorem `lift_original_projection` in the ordinary-import
`SheafCohomologyExamples.NativeCylinderLimitAdditive` specializes the **same**
constructed limit to `C = AddCommGrpCat.{v}`. For arbitrary `m`, `hm`, `U0`,
restricted cone `t` and tail stage `i`, it proves the full sheafed-space arrow
equality

```lean
((restrictedIsLimit N i0 m hm U0).lift t ≫
    m.pt.ofRestrict (coneOpen N i0 m U0).isOpenEmbedding) ≫
      m.π.app (op i.1) =
  t.π.app (op i) ≫ (inclusion N i0 U0).app (op i)
```

The additive client assumes no restricted limit and proves no chosen-limit
comparison or reflection statement.

## Status and provenance

**The original Type-valued history is not this generic contribution.** The
original Type cylinder candidate began from incubator restriction prerequisite
`800f8c79310c54ade745f79d947f98830272f357`, then unaccepted. That
restriction leaf was later accepted without registration (#4/53852). Review
`234e1ae9448fd3eec5bd4250260d9331ebfe8f9a` requested the original
cylinder's attribution repair; independent renewed review
`85aeeef35c3b3f0f01d56869b448a4f49e05f5b5` resolved it. Anchor accepted
only the unregistered Type leaf `bf566ea767083405992cb832df9e914712a9e3cb`
(tree `a159267d83bb32335d17ec42f6d1149622be7e0a`, #4/54011).
The final review tree is `2dcd26c1766fb51af1f960d39a351b7f5f329293`
(`reviews/native-cylinder-limit/REVIEW.md`, #4/54000). Its donor-only
build/axiom evidence `a4d4bfe750d983e9c37598b3dbcefbf848fd348b`
(tree `8c0b6d157a03fe779e6d2be4c8a9add3fdf42c03`) is not a destination
build.

The prior three-payload Type transfer `194e6310aad7205ff53e33cc73e9ba16b5f9398d`
was **assembled at the time** on the unaccepted Sheaf Cohomology candidate
`c45c1713bf3e8457c02730fddf09d810dfae7027` (tree
`c472857b812fd6cf030d7cc58bdc041adcd647f9`). That source-only
77-module successor registered the Type producer and ordinary-import client;
focused destination evidence `b5ac3f80af7ae5bb02d38fb8189bfcea1046469c`
covered its producer/client but did not certify the aggregate roots. Full
77-module CI590 later passed on the original aggregate; it was
**later** individually reviewed, accepted and released: at the 2026-09-27
release checkpoint destination `main` and `release-prep` were
`f15cc3d61ceb85e259b936eb49c1f644d04f88c1`, and the verified official
77 release was `361c79281381d75d3c3c2195947ff8cb3a29c39f` (Sheaf Cohomology
issue #34 comment 55473). On 2026-09-28 actual 79 main/prep advanced to
`f950b52d57e87efb70f4c8adb6d84856248520e9`, native public release
`ca6684a3b2eaa21a9e415175ceda61d9a4ac75c8` (issue #34 comments
55620, 55622, 55625, 55637). That exact commit/tree/sole parent was verified
on actual private GitHub `main` at 00:28:20 UTC (issue #34/55641); the earlier
00:27:50 pending readback is a dated historical checkpoint. Neither the old
assembly's unaccepted status nor subsequent 77/79 decisions accept 85.

The generic native restriction was separately accepted **unregistered** at
`ae8d32640fc9c946778fdd79fbc37528b433fa06` (#4/55201, independent
review `9ce66df6fc29d6386ce9b5d72ca7f9b3bc2bb90e`). On that frozen
prerequisite, Anchor accepted the **unregistered isolated incubator generic
cylinder** `3f42acfa49bc773a4b12727e5f1b68b7299680a7` (tree
`2fb2790a77f9518618a15ffed122fb0d9e1c6c45`) only after complete
seven-module evidence and independent reviews (#4/55575). The guide at this
donor revision describes its earlier candidate status as of 2026-09-27, not
this later acceptance. Original review
`de388e4a01404d58c3afcd9306cb990138ce9f0a` requested changing the
ambiguous phrase “This candidate's author” to **“The original Type cylinder
candidate's author”**; exact-successor independent delta review
`7daf6056828d4231167cd3fa393b5f5823d34519` resolved that sole
provenance objection. The 14-file evidence branch
`85e7799ed3b60bd274fe008989a2bd274763711a` contains the full report,
prebuild matching cache, final seven-target build and complete actual-origin
transitive standard-axiom audits of all 74 kernel declarations, including 25
private ones; interrupted and nonpassing attempts are not successes. These
are **donor**, not destination, proof-integrity results.

At its original 2026-09-28 checkpoint, the generic destination assembly
started at **frozen, unaccepted**
destination `53a0a858ec7d3fab15c96f9f10ba8c31d8e21554` (tree
`ad3a9bb82463fb2739c9bbb4e86fd25676088c52`). Scoped review
`efecfe1`/`native4379` and complete CI637/artifact112464 (#34/55462) close
specific 84 scopes but do not accept 84 or this 85 successor. Static transfer
`2980f5b0fc5c10fa8bf876527366690f8f654a48` (tree
`05cba88aa5c2eea8a8f1da10b28db8a5dd822c3b`) changes only the producer's
restriction import and the additive client's producer import and namespace.
This 2026-09-28 coherent registration adds one ordinary additive-client import
to `SheafCohomologyExamples`; the existing Type client, all producer and client
proofs, and the public root remain unchanged. Traversal reaches 53 producers,
30 client leaves (27 private and three named public), and two roots. At that
assembly no 85 graph build or private-inclusive audit, independent destination
review, parent reconciliation or official publication had occurred. The
ordered 79→81→83→84 predecessors required separate owner decisions.
Neither the donor's seven-module/74-origin evidence (25 private) nor the old
84 CI/review certifies the changed eleven-module closure. No incubator removal,
source correspondence or source coverage follows from static registration.

Subsequently, actual 81 and 83 were released at official private GitHub
`b743039857ca8c206b6a8cdb99afe7c7e8ce0c25` and
`6793f2ff8469d1cab23a98ac2da22a3286d22f8e`. Original frozen 85
`651f8223c7dbb2df870f3f594077365bf6767d7f` passed full both-target,
private-inclusive CI655 (issue #34/comment 55824). Scoped review
`dfd705cfc7a93b9b2164c5f262c9a78093190b73`/native4404 requested
collective-credit correction; exact successor
`7c7c909d3bdad9822697da77032e37fb0e37f297`/native4405 resolved it.
Full changed-header CI674 and fresh final review supported actual accepted
84 main/release-prep `36e49294f84208fa678872e84b6bdbd96c603188` and
official private release `e5d7d6e60243da2ec9a2af243fac3f3a3bf7dc37`
(issue #34/comment 56186), whose sole parent is official 83. This **unaccepted
85** successor inherits that accepted main ancestry and four whole header
repairs while retaining the generic producer, named additive client, Type
client, roots and every module-onward byte from frozen 85. CI655 is not a
changed-header successor check. One applicable both-target/private-inclusive
85 check, fresh author-distinct consolidated actual-parent/main/prep/public
review and separate owner decisions/publication remain. No 85 acceptance,
additive compact-cylinder endpoint, incubator conversion or source coverage
is inferred from these predecessor releases.

**Contributors and dependencies:** The original native open-restriction
predecessor was authored by worker-a Hive Task
`hive-request-dae0d04e8618b53de43730479c4033d21488695b` (UID
`38967a21-9f85-493d-b98f-67dd712fb00e`) at incubator
`800f8c79310c54ade745f79d947f98830272f357`; its reusable destination
module is `SheafCohomology.NativeOpenRestriction`. The subsequent generic
restriction generalization was authored by worker-a Hive Task
`hive-request-30271b71e726fc52aa0a7c7670ba0eca5de6eaac` (UID
`295217cc-fb36-46be-968d-03070242fd2b`), then repaired with a named
additive readback client by worker-a Hive Task
`hive-request-97bfa2a350ebf1a403402c688ba8f4c80ca4a394` (UID
`79c83628-cbc1-4702-a72f-ea4c3412c00d`). The directed-tail inclusion,
directedness, finality and opposite-initiality expressions adapt worker-b Hive
Task `hive-request-065ffb46d5b6d2b9ada197a66b9c1b783b57e00f` (UID
`4720124c-2740-40ba-947d-5be3c681f64e`), originally in
`FormalFrontier/source-fujiwara-kato-rigid-geometry-i`
`e827107b7a1c6a8cf187189bda816f08931e269a`, retained at
`e266a5076df34934171cc284ba8f2834e56f8c78`,
`Research/fk-corollary-3-1-12-open-tail-restriction-scratch.lean:27–49`.
There is no imported source-repository dependency or private source material.
The native-limit/Gamma precursor is in official Sheaf Cohomology release 63
`32b1fb7787d5036c8b7181565a22a460b160f91d`; the mathlib native
open-immersion lift is due to Andrew Yang
(`Mathlib/Geometry/RingedSpace/OpenImmersion.lean`, Apache-2.0).

The original Type cylinder candidate's author is worker-a Hive Task
`hive-request-153a0400bb1a4285602d24cceb51ae9a56b6b3be` (UID
`38e90320-4a49-4738-9620-3881f7b58af5`); the separate header/provenance
repair is by worker-a Hive Task
`hive-request-d984b1de170e87f4be31d9ce565c90299c51e3b3` (UID
`35dd220a-f8a8-4fae-9d05-4a503f2f4b96`), reviewed by worker-b Hive Task
`hive-request-1e8c6a88bf42d9183522899d2ed7cbc7bf9d1916` (UID
`1c65573c-8563-4434-8dbf-138514e62c9a`). The older destination Type
adapter was by worker-a Hive Task
`hive-request-403dd29c9f3677cefb56ce16b370b5872f9bc61a` (UID
`2d67f405-088f-4811-8d5a-6dce4586b1a3`). Route A planning report
`acf16145849b331ef24a9d1d08c671898cd8b466` is by worker-b Hive Task
`hive-request-95f10ba06d205ac6940b05ee7c67b16ff0e0f725` (UID
`df7518ed-d71a-4cb1-b4ab-d6810ad3a1ad`); it is a design, not a proof.
The later **generic** cylinder adaptation and closely adapted named additive
client are by worker-a Hive Task
`hive-request-27d70680c0e69c147294098e3ac13b1c7092c0e1` (UID
`bfe6acf9-1385-4602-a9b8-1e88f6908b1a`). This destination transfer and
guide are by worker-a Hive Task
`hive-request-174ca2aad0df7bdc9275c6af83be955de855bd97` (UID
`abffae59-12f3-4536-8643-d91504fc806d`), **not** authorship of those
original proofs. The distinct coherent root/docs/metadata registration is by
worker-a Hive Task `hive-request-f2b4090a882686df924af77bc982594879d2f8a3`
(UID `bd0b26e2-40ab-4ab0-b12f-60aaf5f4e356`), also not authorship of the
original proofs. Responsible maintainer: Anchor, Sheaf Cohomology issue #34.
The Lean files retain their Apache-2.0 notices and original credits.

A generic chosen-limit/Gamma comparison, spectral extension, additive
compact-cylinder endpoint, assumed restricted `IsLimit` or `IsIso`, and
reflection bridge are outside this API and this transfer.
