# Native restriction to inverse-image opens

Import `SheafCohomology.NativeOpenRestriction` for the public API in
`AlgebraicGeometry.SheafedSpace`. For
`X Y : SheafedSpace.{v + 1, v, v} (Type v)`, a morphism `g : X ⟶ Y`, and
`V : Opens Y`, set `U := (Opens.map g.hom.base).obj V`. No points,
nonemptiness, or extra hypotheses on `V` are needed. The native arrow
`restrictOnPreimage g V` has type

```lean
X.restrict U.isOpenEmbedding ⟶ Y.restrict V.isOpenEmbedding
```

It reuses mathlib's open-immersion lift of the *existing* restriction
inclusions, rather than constructing another sheaf or base-change map.
`restrictOnPreimage_fac` is its commuting inclusion square;
`restrictOnPreimage_unique` characterizes the arrow by that square.
`restrictOnPreimage_base` identifies its literal underlying continuous map
with `TopCat.Sheaf.OpenBaseChange.preimageMap g.hom.base V`.

If a client names an open `U' : Opens X` independently, with
`h : U' = (Opens.map g.hom.base).obj V`, use
`restrictOnNamedPreimage g V U' h`. Its inclusion square and section readback
transport along `h`, rather than silently identifying the two opens.
`restrictOnNamedPreimage_id` and `restrictOnPreimage_comp` give identity and
composition for native arrows after explicit equality transports. In the
composition theorem, `Opens.map_comp_obj` identifies the composite's inverse
image with the iterated inverse image, and the native restriction inclusions
are canceled using their monicity.

`restrict_Γ_obj X U` identifies the global sections of a native restriction
with `X.presheaf.obj (op U)`. Thus `restrictOnPreimage_Γ_map` identifies
`Γ.map (restrictOnPreimage g V).op`, after both `eqToHom` object transports,
with `g.hom.c.app (op V)`. `restrictOnNamedPreimage_Γ_map` also transports
from the canonical inverse-image open to the independently named one.
These results use the actual inclusion square and naturality of the restricted
sheaf morphism; they require no `IsIso` assumption. A representative ordinary
import in `SheafCohomologyExamples.NativeOpenRestriction` composes two
restricted native arrows and recovers the original composite's section
component, including its nondefinitional inverse-image equality cast.

This unit does not establish principal-tail or cylinder limits, restricted
native-limit identifications, colimit-leg naturality, spectral or endpoint
results, converses, or source coverage. The two Lean modules use the pinned
Sheaf Cohomology dependencies and require no incubator import or dependency.

## Provenance and status

The original Apache-2.0 producer/client notices are retained. The original
implementation was authored on September 27, 2026 by Formal Frontier
worker-a Hive Task `hive-request-dae0d04e8618b53de43730479c4033d21488695b`
(UID `38967a21-9f85-493d-b98f-67dd712fb00e`), at exact source revision
`800f8c79310c54ade745f79d947f98830272f357`. Independent worker-b
review by Task `hive-request-4796946df145f280a3210441cf31ddeb69e8fe93`
(UID `d8645b6d-38a8-48fa-a133-7c2a61a0caea`) approved that *unregistered
source leaf* at `1ee5876b03792fabfa806df81a2abe55f94679d4`; responsible
maintainer Anchor accepted the exact unregistered leaf on September 27, 2026.
The present three-file destination adaptation is by worker-a Hive Task
`hive-request-5de3ebfab00e632e44a5c020cb1fd800467bc20f`
(UID `ac4b4dd0-3208-40c0-9352-a602f551452a`). Its producer proof is
unchanged; the example only changes its module import and namespace.

The lift and its factorization and uniqueness come from Andrew Yang's
Apache-2.0 mathlib `Mathlib/Geometry/RingedSpace/OpenImmersion.lean`;
mathlib also supplies the native restriction and `Γ` APIs. The official
Apache-2.0 `SheafCohomology/OpenBaseChange.lean` (Formal Frontier Agents)
supplies the `preimageMap` expression. No private source asset or
source-local experiment was copied.

At the original September 27, 2026 adapter handoff, its target was frozen
**unaccepted** revision `e570bfbb0a56dd38c43e9ed1c10057205e6088aa`, not then
accepted `main`. That is historical target status, not a claim about today's
branches. Its corrected 73-module successor was later independently accepted
and released as official `6aa8528f28264d9b44de0f31e72696d8d95ce97d`, verified
at 21:19:58 UTC that day. The 75-module reconciliation normally merged the
accepted main ancestry, retaining both transferred Lean blobs unchanged.

The full 75-module check on `c45c1713bf3e8457c02730fddf09d810dfae7027`
succeeded at 19:45:26 UTC, and its complete build and private-inclusive
standard-axiom evidence was inspected by the owner. Unchanged computational
inputs permitted reuse, not a claim of a fresh successor build or audit.
The corrected candidate `efcfeae07fa909b9c1d20bdd665cf733eb11cb4d` later
passed full CI621 at 22:20:06 UTC. After complete owner evidence intake,
independent final review and individual main/prep/public decisions and protected
integration, its official GitHub release
`57decc6d5106fe32dc57f9684de38f6e10534de5` was verified at 22:30:32 UTC.
Those decisions concern the 75-module contribution, not later successors.
Source coverage and any incubator conversion are
separate; none follows merely from the accepted source leaf or this adapter.
