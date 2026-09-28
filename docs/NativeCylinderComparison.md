<!-- SPDX-License-Identifier: Apache-2.0 -->
# Chosen native cylinder limits and original-stage sections

Import `SheafCohomology.NativeCylinderComparison` directly, or use the aggregate
`SheafCohomology` root, which re-exports this module since the 79-module release. This is a
reusable comparison for actual native limits, not an alternative diagram or a
spectral invertibility theorem.

## Data and chosen native comparison

Fix `ι : Type v` with `[Preorder ι] [IsDirectedOrder ι]`, an explicit
`i0 : ι`, a diagram
`N : ιᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace.{v + 1, v, v} (Type v)`, and an
*actual* cone `m : Cone N` with `hm : IsLimit m`. Choose any
`U0 : Opens (N.obj (op i0))`; it may be empty. The principal tail
`Set.Ici i0` is inhabited by `i0` and filtered by the directed preorder,
without a linear-order or nonempty-open hypothesis. The inherited
`restricted N i0 U0` uses the actual native open restrictions, and
`restrictedCone N i0 m U0` has the literal restriction of `m.pt` as its
vertex.

`restrictedSpaceIsLimit N i0 m hm U0` applies the published
`SheafedSpace.preservesLimitForgetOfHasLimit` to the inherited *native*
`restrictedIsLimit`. It supplies the forgotten-space limit needed by the
published `SheafedSpace.limitConeOfSpaceCone`; it is not a general assertion
that forgetting an arbitrary native limit preserves it. Write `Q` for this
chosen native limit and `R` for `restrictedCone N i0 m U0`. Then
`chosenLimitIso N i0 m hm U0 : Q.cone.pt ≅ R.pt` compares the chosen
construction with the literal restriction. The theorems
`chosenLimitIso_hom_projection` and `chosenLimitIso_inv_projection` give
both native projection equations, not just equations of underlying spaces.
`chosenLimitIso_hom_base` and `chosenLimitIso_inv_base` additionally state
that both underlying base maps are the identity on the literal cylinder
space, by the forgotten limiting cone's hom-extensionality.

## Contravariant sections and exact stage law

`restrictedGlobalSectionsComparison N i0 m hm U0` maps the colimit of
the *actual restricted-stage* global sections to
`m.pt.presheaf.obj (op (coneOpen N i0 m U0))`. It composes
`SheafedSpace.nativeGlobalSectionsComparison` for `Q`,
`SheafedSpace.Γ.map (chosenLimitIso N i0 m hm U0).inv.op`, and the
`eqToHom` from `SheafedSpace.restrict_Γ_obj` for `R.pt`.
The **inverse** is needed because `Γ` reverses native arrows; no desired
`IsIso` premise is introduced.

`colimit_ι_restrictedGlobalSectionsComparison` identifies each colimit
leg with `Γ.map` of the actual restricted-cone projection followed by
the restriction-object `eqToHom`. More precisely,
`originalStage_restrictedGlobalSectionsComparison` precomposes that leg
with the *inverse* stage restriction-object cast
`eqToHom (SheafedSpace.restrict_Γ_obj (N.obj (op i.1))
  (stageOpen N i0 U0 i)).symm`. Its right-hand side is the actual
original native projection's presheaf component
`(m.π.app (op i.1)).hom.c.app (op (stageOpen N i0 U0 i))`, followed by
`eqToHom` of the inverse-image-open equality
`(coneOpen_eq_stage N i0 m U0 i).symm` after applying
`fun W : Opens m.pt => m.pt.presheaf.obj (op W)`. These casts are explicit;
the original stage is not silently identified with its native restriction.

`SheafCohomologyExamples.NativeCylinderComparison` uses an ordinary
`import SheafCohomology.NativeCylinderComparison`. Its private theorem
`chosen_projection_and_original_stage` simultaneously uses the inverse
native projection law, both base identities and the exact original-stage
section equation for arbitrary `U0`, including the empty case. It does
not posit a restricted limit or a section law as a hypothesis.

## Reproduction, attribution and status

The pinned environment uses Lean `leanprover/lean4:v4.34.0-rc2`, mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, official Spectral14
`452b7b7be1bea76434cd083b1019a26f96b4ab30` and inherited official
Ideal `001e3b7508184ecd51e0d86177cb1d54508bf59d`. After installing
the pinned toolchain and successfully fetching `lake exe cache get` from
the repository root, the focused targets are
`lake build SheafCohomology.NativeCylinderComparison
SheafCohomologyExamples.NativeCylinderComparison`. Neither Lean file nor
this repository's manifest depends on incubator.

Both complete Lean statements **and proof expressions** come from
`FormalFrontier/incubator` commit
`139b78367cd641f86c1ccf489f1898db3fab32e4` (tree
`319ebc40930d3be157e4e923fec144bf47d0a375`), files
`Incubator/Topology/Sheaves/NativeCylinderComparison.lean` (blob
`76263b70a75ba132e0de4acc3bfe949dfb556457`) and
`IncubatorTest/Topology/Sheaves/NativeCylinderComparison.lean` (blob
`9c4f0b8bc2a09974a86bba547c191f0decf949de`). Reversing only the
two producer public-import replacements, and only the client import and
namespace/end replacements, recovers those exact blobs. The Apache-2.0
SPDX and collective authorship notices are retained.

The original comparison and complete proof expressions are by worker-b
Hive Task `hive-request-f9876d0c2840470583113050ec0546a64eb3954f`
(UID `91e70b6b-63f7-4c56-846f-b66316065a3c`), author revision
`854e446c6b0efbf85c3023e7b21ccd7f9428d8ea`. Fresh independent
worker-a reviewer `hive-request-0b6d132e6ccf9833cd02ade98d31770d2a5ab1e1`
(UID `73f1fb4c-cd23-4deb-afbc-579c3ef3cee7`) recorded the review
at `FormalFrontier/incubator` commit
`c2c9ac564f69514bbbebbdd03945c95b19c9f7e9`,
`reviews/native-cylinder-comparison/REVIEW.md`; Anchor reconciled its
preserved author branch with accepted-unregistered cylinder parent
`bf566ea767083405992cb832df9e914712a9e3cb`. Donor-focused evidence
is commit `da4acd9e9915d3223b5fddbbc297b5702ea264cb` in that
repository; it does **not** compile or audit the destination modules.
This destination import/namespace adapter and guide are by worker-a Task
`hive-request-4ea69b252477c9247909ab3e36e3c4b4134edbbb`
(UID `d0fb2e2c-6071-47c1-8e8d-f552d91874a4`).

The inherited cylinder mathematics is by worker-a Task
`hive-request-153a0400bb1a4285602d24cceb51ae9a56b6b3be`
(UID `38e90320-4a49-4738-9620-3881f7b58af5`); its provenance repair
is by worker-a Task `hive-request-d984b1de170e87f4be31d9ce565c90299c51e3b3`
(UID `35dd220a-f8a8-4fae-9d05-4a503f2f4b96`). The adapted
tail-directedness proof expressions trace to worker-b Task
`hive-request-065ffb46d5b6d2b9ada197a66b9c1b783b57e00f`
(UID `4720124c-2740-40ba-947d-5be3c681f64e`), original
`FormalFrontier/source-fujiwara-kato-rigid-geometry-i` commit
`e827107b7a1c6a8cf187189bda816f08931e269a`, retained at
`e266a5076df34934171cc284ba8f2834e56f8c78`,
`Research/fk-corollary-3-1-12-open-tail-restriction-scratch.lean:27–49`.
Native restriction predecessor `800f8c79310c54ade745f79d947f98830272f357`,
native Γ predecessor `00d551efc598b8252fbc694830523b830bf94a27`,
official Sheaf63 `32b1fb7787d5036c8b7181565a22a460b160f91d`
and mathlib's native restrictions/open-immersion lift (Andrew Yang,
`Mathlib/Geometry/RingedSpace/OpenImmersion.lean`, Apache-2.0) are
credited further in `docs/NativeCylinderLimit.md`,
`docs/NativeOpenRestriction.md` and `docs/NativeLimitGlobalSections.md`.

**Lifecycle on 2026-09-27:** Anchor accepted donor `139b78367cd641f86c1ccf489f1898db3fab32e4`
as an **unregistered incubator leaf only**, at incubator issue #4/comment
54410. This adapter started from the then **unaccepted** destination
`c2809532ab73025867cb24b8b80d9e67da069d2d` (Sheaf77), with
expected rework if that parent changed. Anchor's subsequent source-only
79-module registration preserves both transferred Lean blobs, adds aggregate
producer/client imports and updates navigation, metadata and credit. At its
20:19:12 UTC assembly it was not independently reviewed, accepted, merged or
released. Destination-focused evidence at
`a5c49fc6f3e083b4324d593c1793071afa4fe6e5` is separate from donor evidence;
it did not certify the changed roots. Later scoped independent review
`5d8e1855fdd7aa2f1aab97157dd745b7e9f484be` approved the mathematical,
API, provenance and registration increment. Full 79-module CI607 on
`d443e034746972593ec0c91f64268771a3013b5a` succeeded at 21:37:56 UTC;
the owner inspected its complete both-target build and private-inclusive
standard-axiom evidence. The corrected 77-module predecessor later completed
its own review, full CI633, owner decisions and protected integration; official
GitHub release `361c79281381d75d3c3c2195947ff8cb3a29c39f` was verified
at 23:41:14 UTC. The documentation-only 79-module successor normally merged its accepted
main `f15cc3d61ceb85e259b936eb49c1f644d04f88c1`, retaining all 79 Lean
blobs, roots, eleven package objects and CI inputs. Full CI643 on the corrected
`f950b52d57e87efb70f4c8adb6d84856248520e9` succeeded on 2026-09-28
at 00:18:28 UTC. Complete owner evidence intake and final independent review
`9e7df0cc74e4b612f72201b8baec304a281228ce` preceded separate main,
release-prep and public owner decisions and protected integration. Its official
GitHub release `ca6684a3b2eaa21a9e415175ceda61d9a4ac75c8` was verified
at 00:28:20 UTC. These are this comparison contribution's own decisions,
not acceptance of later spectral or additive extensions. No spectral `IsIso`, endpoint, source-passage
correspondence or formalization-coverage conclusion is claimed.
