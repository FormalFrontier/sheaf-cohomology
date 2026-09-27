# Native limits of principal-tail open cylinders

Import `SheafCohomology.NativeCylinderLimit` for the API in
`AlgebraicGeometry.SheafedSpace.NativeCylinderLimit`. The separate
`SheafCohomologyExamples.NativeCylinderLimit` is an ordinary-import client;
neither module imports the incubator or a source-research repository.

Let `ι : Type v` be a preorder with `IsDirectedOrder ι`, let `i0 : ι` be an
**explicit** distinguished index, and let
`N : ιᵒᵖ ⥤ SheafedSpace.{v + 1, v, v} (Type v)`. Given a native cone
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
  open; `coneComponent` uses the named-preimage native restriction arrow,
  and `coneComponent_fac` records its commuting native inclusion square.
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
takes *any* `t : Cone (restricted N i0 U0)` and any tail stage
`i : Set.Ici i0`, applies `(restrictedIsLimit N i0 m hm U0).lift t`, and
recovers its original-projection equation after composing with the native
restriction inclusion. It neither posits the desired restricted `IsLimit`
nor replaces the diagram with an alternate model.

## Status and provenance

The three-payload transfer `194e6310aad7205ff53e33cc73e9ba16b5f9398d`
was assembled on the frozen, unaccepted Sheaf Cohomology candidate
`c45c1713bf3e8457c02730fddf09d810dfae7027`
(tree `c472857b812fd6cf030d7cc58bdc041adcd647f9`), not then accepted
deliverable `main` or an official release. At the original 2026-09-27
19:11:29 UTC assembly, the source-only 77-module successor registered its
unchanged producer and client in the existing aggregate targets, with navigation,
credit and metadata. The parent was unaccepted at that snapshot. Separate destination-focused evidence
`b5ac3f80af7ae5bb02d38fb8189bfcea1046469c` records matching cache,
warning-fatal producer/client builds and all 41 new actual kernel origins,
including private declarations; it does not certify the changed aggregate roots.
Full 77-module CI590 on `c2809532ab73025867cb24b8b80d9e67da069d2d`
subsequently succeeded at 20:37:50 UTC; the owner inspected its complete
both-target build and private-inclusive standard-axiom evidence. The corrected
75-module predecessor later completed its own independent review, full CI621,
owner decisions and protected integration; its official GitHub release
`57decc6d5106fe32dc57f9684de38f6e10534de5` was verified at 22:30:32 UTC.
Its documentation-only reconciliation normally merged accepted main
`efcfeae07fa909b9c1d20bdd665cf733eb11cb4d` without changing any of the
77 Lean blobs, roots, eleven package objects or CI inputs. Full CI633 on corrected
`f15cc3d61ceb85e259b936eb49c1f644d04f88c1` succeeded at 23:30:34 UTC;
complete owner intake is recorded in Sheaf Cohomology issue #34/comment 55429.
After final independent review `4234805eb8b0fe43059c2cab212d0d3d06d2c38e`
and separate main/prep/public owner
decisions and protected integration, official GitHub release
`361c79281381d75d3c3c2195947ff8cb3a29c39f` was verified at 23:41:14 UTC
(issue #34/comment 55473). These decisions accept the 77-module contribution,
not its comparison successor or source coverage.
The exact incubator donor
`bf566ea767083405992cb832df9e914712a9e3cb` (tree
`a159267d83bb32335d17ec42f6d1149622be7e0a`) was accepted by
responsible maintainer Anchor **only as an unregistered leaf**, incubator
issue #4 comment 54011. Independent final worker-b review
`85aeeef35c3b3f0f01d56869b448a4f49e05f5b5` (tree
`2dcd26c1766fb51af1f960d39a351b7f5f329293`,
`reviews/native-cylinder-limit/REVIEW.md`, issue #4 comment 54000)
resolved the earlier `234e1ae9448fd3eec5bd4250260d9331ebfe8f9a`
REQUEST_CHANGES about headers and attribution; those objections and their
resolution are preserved. Applicable donor-only build/axiom evidence is
`a4d4bfe750d983e9c37598b3dbcefbf848fd348b` (tree
`8c0b6d157a03fe779e6d2be4c8a9add3fdf42c03`). It is **not** a
destination build. The transferred Lean source changes only its parent
import; the client changes only its import and namespace. Both retain the
original Apache-2.0 SPDX and collective project-author notices.

The native open-restriction predecessor was authored by worker-a Hive Task
`hive-request-dae0d04e8618b53de43730479c4033d21488695b` (UID
`38967a21-9f85-493d-b98f-67dd712fb00e`), at incubator commit
`800f8c79310c54ade745f79d947f98830272f357`; the independently usable
destination predecessor is `SheafCohomology.NativeOpenRestriction`.
The directed-preorder tail inclusion, directedness, finality and
opposite-initiality expressions adapt Formalization Worker B Hive Task
`hive-request-065ffb46d5b6d2b9ada197a66b9c1b783b57e00f` (UID
`4720124c-2740-40ba-947d-5be3c681f64e`), originally in
`FormalFrontier/source-fujiwara-kato-rigid-geometry-i` commit
`e827107b7a1c6a8cf187189bda816f08931e269a`, retained at
`e266a5076df34934171cc284ba8f2834e56f8c78`,
`Research/fk-corollary-3-1-12-open-tail-restriction-scratch.lean:27–49`.
No source-repository dependency or private source material is imported.
The native-limit/Gamma precursor is in official Sheaf Cohomology release 63
`32b1fb7787d5036c8b7181565a22a460b160f91d`; mathlib supplies the
native restrictions and open-immersion lift (Andrew Yang,
`Mathlib/Geometry/RingedSpace/OpenImmersion.lean`, Apache-2.0).

The cylinder mathematics was authored by worker-a Hive Task
`hive-request-153a0400bb1a4285602d24cceb51ae9a56b6b3be` (UID
`38e90320-4a49-4738-9620-3881f7b58af5`); its headers/provenance were
repaired by separate worker-a Hive Task
`hive-request-d984b1de170e87f4be31d9ce565c90299c51e3b3` (UID
`35dd220a-f8a8-4fae-9d05-4a503f2f4b96`), and independently reviewed
by worker-b Hive Task `hive-request-1e8c6a88bf42d9183522899d2ed7cbc7bf9d1916`
(UID `1c65573c-8563-4434-8dbf-138514e62c9a`). This three-payload
adapter is by worker-a Hive Task
`hive-request-403dd29c9f3677cefb56ce16b370b5872f9bc61a` (UID
`2d67f405-088f-4811-8d5a-6dce4586b1a3`). Responsible maintainer:
Anchor, Sheaf Cohomology issue #34.

Incubator conversion and any source correspondence/coverage decision remain
separate from the recorded 77-module release. A chosen-limit isomorphism,
Gamma comparison, spectral transfer and IsIso endpoint are outside this API.
Changed prerequisite APIs require reassessment. The predecessor release and
original 77-module computation do not supply any later successor's separate owner decisions.
