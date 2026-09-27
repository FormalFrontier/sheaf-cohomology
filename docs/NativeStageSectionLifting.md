<!-- SPDX-License-Identifier: Apache-2.0 -->

# Native lifting of sections to a filtered stage

Import `SheafCohomology.NativeStageSectionLifting`. Let `J : Type v` be a
small filtered category, `N : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace (Type v)` a
diagram whose underlying spaces are spectral and whose underlying transition
maps are spectral, and let `c` be a limiting cone over its underlying
topological diagram. The theorem
`AlgebraicGeometry.SheafedSpace.exists_native_stage_section_lift` accepts a
stage `i : J` and an element `s` of the **actual** cone-pullback sheaf's global
sections at `i`. It produces `j : J`, `g : i ⟶ j`, and a native global section
`a : (N.rightOp ⋙ AlgebraicGeometry.SheafedSpace.Γ).obj j` satisfying the
literal equation

```lean
(SheafCohomology.ConePullbackSections.coneSections N c).app j a =
  (AlgebraicGeometry.SheafedSpace.conePullback (Type v) N c ⋙
    SheafCohomology.CompactOpenSections.sectionsOf (⊤ : Opens c.pt)).map g s
```

The hypotheses are a small filtered index category, a limiting cone for the
underlying spaces, spectral stage spaces, and spectral transition maps. No
stage-inhabitedness, nonempty cover, preorder, transition injectivity or
endpoint-isomorphism hypothesis is required. In particular, the empty-indexed
finite cover and empty-stage cases use the existing sheaf condition and do not
choose a point. This proves an element-level later-stage lift, **not** a
filtered-colimit comparison, endpoint isomorphism, or source-coverage claim.

The proof represents the cone-pullback section on a finite compact-open
cover, descends that cover to one whole native stage, transports the actual
projection-unit equalities through the restricted adjoint triangle, synchronizes
finite overlap equalities on a coherent filtered wide span, glues native local
sections, and recovers the given pullback section by sheaf separatedness. The
finite synchronization, transport, and gluing lemmas are private; the lifting
theorem is public. This is the existing native `SheafedSpace.Γ` functor and the
existing cone-section transformation, not a replacement stage functor.

For ordinary clients, `import SheafCohomology.NativeStageSectionLifting` suffices.
`SheafCohomologyExamples.NativeStageSectionLifting` uses an **ordinary** import
and has two **private** declarations: a later native section exists, and the
chosen lift remains valid after every further native arrow by naturality.
They are example clients, not additional public APIs. The producer's `public
import` declarations describe its imported modules, not the visibility of these
private client declarations. The producer additionally imports
`SheafCohomology.NativeStageSectionEquality`,
`SheafCohomology.ConePullbackSections`,
`SpectralStoneDuality.FiniteCylinderDescent`, and
`SpectralStoneDuality.Limits` as public imports. The destination uses pinned
Lean `v4.34.0-rc2`, mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5`,
official Spectral14 `452b7b7be1bea76434cd083b1019a26f96b4ab30`
(inheriting official Ideal `001e3b7508184ecd51e0d86177cb1d54508bf59d`),
and the local sheaf modules; no incubator or source checkout is a dependency.
From the repository root, fetch the matching cache **before** the focused build:

```sh
lake exe cache get
lake build SheafCohomology.NativeStageSectionEquality SheafCohomology.ConePullbackSections SheafCohomology.NativeStageSectionLifting SheafCohomologyExamples.NativeStageSectionLifting
```

## Provenance and status

The **full original producer and client proof expressions are copied and
mechanically transferred**, not just inspired by an idea. The originals are
incubator commit `055857c06b98686dfc9f33f77f401f1dda2cc150` (tree
`8c3ce66a811028043fce875d0dd86ad6f84e0ddc`), blobs
`9b11134348177180ad1855660691d87ac52ffe71` and
`cd56b7c16a5fdb68977b7db20ec0c32506235d63`. The only producer change
is its equality-module import; the only client changes are its ordinary import
and namespace/end. Reversing those substitutions reproduces both blobs.
Original implementation: worker-b Hive Task
`hive-request-e5e544a630e9b84215130384682791cdebd0aea0` (UID
`3bb51737-f69e-4698-9538-9f0336c572d9`); original independent review:
worker-a Hive Task `hive-request-9639b5e9869b8855e5090d224960c07301b3aa4e`
(UID `7a8d0f31-e6c4-47d6-95e2-ac99a9886260`), review commit
`3759f8ed0fb4c2c07b330916a7448acad51ee7d5` at
`reviews/native-stage-section-lifting/REVIEW.md`; original unchanged-input
evidence `0f334e3b76ddc4d079f7aaea7f6a75cdebe7e6da`.

Mathematical motivation and whole-stage descent design are due to Anchor;
the equality leaf is by worker-b Task
`hive-request-83333dedd640d855f159f1c115a70d659ba2c7dc`,
native local-unit representation by Anchor and worker-b Task
`hive-request-c862e7aa8f5b10a37f55dbfbfcc07250a83772cd`,
cone-section transport and adapters include worker-a Task
`hive-request-56a0f46868a5a666cdc4e1ce2d7423802e462456`,
finite-cylinder stage cover includes worker-b Task
`hive-request-1365e777e728ab94ed1310b0b8cf71258cc1e36b`,
and synchronization/gluing API design was investigated by worker-a Task
`hive-request-0345c343859e7ae47299b71afc5cd98141de8afb` (UID
`fdef243b-96f9-48cf-b6ec-799e8f54ee8f`). The owner-provided descent
design is recorded at incubator `5e0fd2eef84674cec6ade0a6f1ea1ca5ebe40d24`.
The narrow destination adapter and this guide are by worker-a Hive Task
`hive-request-ed4ccda04a6ba2607731fe00b73853080a0f5761` (UID
`9aa315b6-c463-47b1-a6cb-7cd8989f4f72`). Credit does not assert source
correspondence or acceptance of the destination.

The unchanged producer and private-client Lean leaves are now registered in
the two existing default-target roots as part of the source-only 69-module
candidate. Its frozen Sheaf67 predecessor
`e2b368027e83268263317b87bdd9b9e210db8021` was **unaccepted** at assembly;
its own acceptance and release gates remain separate. The changed roots are
new computational inputs. Focused checks do not establish a full-root build,
independent destination review, owner acceptance, integration, or verified
release of this candidate. Those decisions and later incubator conversion
remain the responsible maintainer's separate work.
