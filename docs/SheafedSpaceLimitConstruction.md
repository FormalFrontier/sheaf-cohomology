# Native sheafed-space limits from sheaf colimits

Import `SheafCohomology.LimitConstruction`. For
`S : Jᵒᵖ ⥤ AlgebraicGeometry.SheafedSpace A`, supply an **actual** space cone
`c : Cone (S ⋙ SheafedSpace.forget A)` and `hc : IsLimit c`. Then

```text
SheafedSpace.limitConeOfSpaceCone A S c hc : LimitCone S
```

constructs a *named native limiting cone*, rather than testing a hypothetical
native cone or assuming its `IsLimit`. The construction requires
`[HasColimitsOfShape J A]` and
`[HasWeakSheafify (Opens.grothendieckTopology c.pt) A]` in addition to the
predecessor's concrete-coefficient hypotheses. These are coefficient
shape-colimit and sheafification assumptions at the **actual chosen space**;
they are not assumptions about limits of sheafed spaces or about a presupposed
colimiting cocone of sheaves.

## Construction and readbacks

`conePullback A S c : J ⥤ c.pt.Sheaf A` is the predecessor's diagram of
inverse images along the *actual* projections `c.π.app (op i)`. In the scope
of `conePullbackColimitCocone`, mathlib's
`CategoryTheory.Sheaf.instHasColimitsOfShape` is installed explicitly as a
**local** instance for the site `Opens.grothendieckTopology c.pt`. The
`TopCat.Sheaf` wrapper does not synthesize this instance automatically at
these pins. The resulting `conePullbackColimitCocone A S c` is definitionally
`colimit.cocone (conePullback A S c)` with that local instance;
`conePullbackColimitCocone_isColimit` uses `colimit.isColimit` for this
**specific** cocone. No generic replacement sheaf-colimit theorem or global
orphan instance is introduced.

The `coneOfPullbackCocone` predecessor reconstructs a native cone
using this cocone, and its
`coneOfPullbackCoconeIsLimit` proves the native universal property from
`hc` and the actual sheaf `IsColimit`. This reuses the real base-change,
adjunction-mate, triangle and uniqueness proofs; this leaf does not reprove
them or assume a native limit.

The following public readbacks preserve the exact selected base and legs:

```text
limitConeOfSpaceCone_carrier      : ((limitConeOfSpaceCone A S c hc).cone.pt : TopCat) = c.pt
limitConeOfSpaceCone_sheaf        : (limitConeOfSpaceCone A S c hc).cone.pt.sheaf
                                  = (conePullbackColimitCocone A S c).pt
limitConeOfSpaceCone_sheaf_colimit : sheaf = (colimit.cocone (conePullback A S c)).pt
limitConeOfSpaceCone_forget       : (forget A).mapCone (limitConeOfSpaceCone A S c hc).cone = c
limitConeOfSpaceCone_π_base       : projection.hom.base = c.π.app i
limitConeOfSpaceCone_π_mate       : sheafMate A projection
                                  = (conePullbackColimitCocone A S c).ι.app (unop i)
limitConeOfSpaceCone_π_mate_colimit_ι : sheafMate A projection
                                  = colimit.ι (conePullback A S c) i
```

The two rightmost terms are elaborated under precisely the same *local* site
sheaf colimit instance. No equality of sheaves or legs over unequal base
spaces is implied; the predecessor's transport handles that dependency.

If a base limit is already selected by `[HasLimit (S ⋙ forget A)]`, and
`[HasWeakSheafify (Opens.grothendieckTopology
  (limit (S ⋙ forget A))) A]` holds, then
`hasLimitOfHasLimitForget A S : HasLimit S` chooses `limit.cone` and its
`limit.isLimit` and applies the same constructor. This is a **named**
`HasLimit S` witness, not an assumption or a registered global instance.

## Shape and coefficient boundaries

The base construction preserves `A : Type u`, `Category.{w} A`, and independent
`J : Type wj`, `Category.{vj} J` of the predecessor APIs. The
coefficients must admit `FunLike`/`ConcreteCategory.{w}` with concrete carrier
in `Type w`, `HasColimits A`, `HasLimits A`, and preservation of limits and
filtered colimits and reflection of isomorphisms by `CategoryTheory.forget A`.
The extra `[HasColimitsOfShape J A]` is explicit because the ambient
`[HasColimits A]` alone need not supply an arbitrarily large index shape.
`[HasWeakSheafify]` is required at the vertex actually being used, not at
every possible space. The chosen-base witness uses the concrete-carrier
universe in `SheafedSpace.{u,w,w} A`; it does not silently impose a bound on
`wj` or `vj`. These hypotheses **do not claim** limits for all unrestricted
large diagrams or assert a global `HasLimits` instance.

The import-only client
`SheafCohomologyExamples.LimitConstruction` constructs actual
`LimitCone` values for arbitrary `Type v` and `AddCommGrpCat.{v}` diagrams
over `(Fin 3)ᵒᵖ`, verifies both arrows `0 ⟶ 1`, `1 ⟶ 2`, their composite,
actual inverse-image projection mates and the corresponding `colimit.ι` legs,
and exercises the chosen-base `HasLimit` witnesses. The arrows have distinct
endpoints; there is **no** claim that an arbitrary diagram sends them to
nonidentity maps.

For the genuine empty-index case the client builds its own
`PEmptyᵒᵖ ⥤ SheafedSpace (Type 0)` diagram and a space cone on
`TopCat.of PUnit.{1}`. `TopCat.isTerminalPUnit` supplies an actual
`IsLimit` of that space cone. The local site-sheaf construction produces the
empty sheaf colimit; the client proves both its `IsColimit` and its
`IsInitial` (by uniqueness of maps out of the empty colimit point). Applying
the producer then constructs an actual empty native `LimitCone`. No desired
native `IsLimit` or separately assumed sheaf `IsColimit` appears as a client
input.

## Provenance and lifecycle

The original mathematical construction is the accepted three-file contribution at
`f30d2befa872ce170736d97a72444790847365e5` (tree
`ea22300345b34c2c7536fb7d9b4763955ba9794e`), by Worker A Hive Task
`hive-request-700e4f0e3debb32b4538a1158e70ca099e66c254`, UID
`02943c65-933d-4b1e-974b-decbd5d5f153` (Forgejo identity
`formalization-worker-a`). Its independent mathematical review is Worker B
Hive Task `hive-request-f56d422e9bac1b8c13465b1dc849cc5f891a493a`,
UID `2eedc5aa-54f0-479d-a611-70a1049ec996`, report revision
`c8a4369a1b025cd658807ebdaaa21084e6e5432c`. The producer proof
expressions and public statements are unchanged in this transfer. The
destination transfer is by Worker A Hive Task
`hive-request-6dd6bbaa5fa6642467da4af8d0dff8a12786d1c4`, UID
`b6d76148-1649-49aa-943e-731466986081` (Forgejo identity
`formalization-worker-a`). No source asset is used.

The transfer is prepared against frozen destination base
`ce1675379e204c8d6d40a5f30b40942640ed25bd`, an **unaccepted**
53-module assembly. The earlier mathematical review does not review the
adapted files or the combined destination graph. As of September 27, 2026,
Anchor's successor registers the unchanged production and private-client Lean
files in the aggregate roots and adds navigation, contributor credit and scope
metadata. This 55-module assembly and its 53-module predecessor remain
unaccepted, not integrated into destination `main` and not released. Exact
independent destination/release assessment and an applicable combined build
and complete private-inclusive standard-axiom audit remain required. Earlier
leaf checks are not a combined-root check. The responsible maintainer owns
acceptance, integration and ordered verified release; changed prerequisites
or pins require renewed evidence applicability checks and may require rework.
This module does **not** provide a converse criterion, coefficient-forget
compatibility, Ringed/scalar extensions, source-specific endpoints or
correspondence, or a source-formalization decision.

With the repository's pinned Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`, run from the project root:

```sh
lake exe cache get
lake --no-ansi --wfail build SheafCohomology.LimitConstruction SheafCohomologyExamples.LimitConstruction
```

The separate transfer evidence reports the exact matching-cache result,
warning-fatal affected build and complete transitive standard-axiom collector
over both new module origins, including private/generated client declarations.
These checks do not replace independent destination review or establish a
registered default-root build.
