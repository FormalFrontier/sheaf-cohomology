# Square transitions for sheaves

[`SheafCohomology/SquareTransition.lean`](../SheafCohomology/SquareTransition.lean)
provides `TopCat.Sheaf.SquareTransition` for a commuting square of continuous
maps

```text
Xj --p--> Xi          p ≫ fi = fj ≫ q
 |         |
 fj        fi
 |         |
 v         v
Yj --q--> Yi
```

For sheaves `F : Xi.Sheaf A` and `G : Xj.Sheaf A`, a stage map
`a : (pullback A p).obj F ⟶ G` determines

```lean
transition A p q fi fj h a :
  (pullback A q).obj ((pushforward A fi).obj F) ⟶
    (pushforward A fj).obj G
```

This is the literal counit-defined transition, not a transition assumed from
an unspecified base-change isomorphism. Its `q`-adjoint satisfies the *forward*
strict pushforward-mate formula

```lean
adjoint A q (transition A p q fi fj h a) =
  (pushforward A fi).map (adjoint A p a) ≫
    (pushforwardSquareIso A p q fi fj h).hom.app G
```

The native mate and the strict comparison agree as isomorphisms; neither the
comparison nor its inverse is a hypothesis. No spectral-space, nonempty-space
or compatibility condition on the original stage map is needed. Equality of
the square's composites is needed only as `h : p ≫ fi = fj ≫ q`.

## Coefficients and universes

The coefficient objects form `A : Type u` with `[Category.{w} A]`. The spaces
and their morphisms are `TopCat.{w}`; the concrete coefficient **carriers** and
coefficient morphisms also live in universe `w`. The coefficient **object**
universe `u` remains independent. The actual ambient assumptions are:

```lean
{FA : A → A → Type*} {CA : A → Type w}
[∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
[ConcreteCategory.{w} A FA] [HasColimits A] [HasLimits A]
[PreservesLimits (CategoryTheory.forget A)]
[PreservesFilteredColimits (CategoryTheory.forget A)]
[(CategoryTheory.forget A).ReflectsIsomorphisms]
```

These are the assumptions of the native sheaf pullback adjunction; they are
not interchangeable with an arbitrary category of coefficients. In particular,
the examples instantiate `A` with `Type v` and `AddCommGrpCat.{v}` under their
respective mathlib instances. The supporting identity/composition pullback
comparisons are in
[`SheafCohomology/PullbackCoherence.lean`](../SheafCohomology/PullbackCoherence.lean).

## Public API

All 25 declarations below are in `TopCat.Sheaf.SquareTransition` and take
the coefficient category `A` explicitly. See the linked source for exact
implicit arguments, statement types and available instances.

| Declaration | Meaning |
| --- | --- |
| `adjoint` | Adjoints a map out of `p`-pullback to a map into `p`-pushforward. |
| `identity` | Canonical identity-pullback stage morphism. |
| `composite` | Composes consecutive stage maps using the *inverse* canonical composite-pullback comparison. |
| `pullbackEqIso` | Contravariant equality transport `pullback A b ≅ pullback A a` for `a = b`. |
| `pullbackEqIso_hom` | Identifies that transport's forward component with `eqToHom`. |
| `pushforwardEqIso` | Covariant equality transport `pushforward A a ≅ pushforward A b`. |
| `pushforwardEqIso_hom` | Identifies its forward component with `eqToHom (congrArg (pushforward A) h)`. |
| `pushforwardCompIso` | Records the *definitionally strict* composite-pushforward comparison as an isomorphism. |
| `pullbackSquareIso` | Pullback comparison formed from composite-pullback isomorphisms and equality transport. |
| `pullbackComparison` | Componentwise literal pullback comparison for one sheaf on `Yi`. |
| `pullbackComparison_eq_iso_app` | Identifies the literal comparison with the natural-isomorphism component. |
| `pushforwardSquareMateIso` | Right-adjoint conjugate of `pullbackSquareIso`. |
| `pushforwardSquareIso` | *Forward* strict pushforward comparison using composition and equality transport. |
| `pushforwardSquareIso_hom_eq` | Identifies its forward natural transformation with `eqToHom` of the composite equality. |
| `pushforwardSquareMateIso_eq` | Proves the mate is the forward strict comparison, not its inverse. |
| `mate` | Constructs the counit-based map before adjunction across `fj`. |
| `transition` | Applies the `fj` adjunction to `mate` to obtain a map across `q`. |
| `transition_adjoint` | The inverse `fj` adjunction sends `transition` back to `mate`. |
| `transition_proof_irrel` | The transition is independent of the chosen proof of square commutativity. |
| `adjoint_transition` | States the displayed forward `q`-adjoint mate formula. |
| `transition_comp` | Naturality in the stage target: postcomposition by `b : G ⟶ H` maps to postcomposition by `(pushforward A fj).map b`. |
| `adjoint_identity` | The canonical identity-pullback stage map adjoints to the identity. |
| `adjoint_composite` | Adjoint of a composite stage map is the first adjoint followed by pushforward of the second. |
| `transition_identity` | Transition across the square of identity stage maps preserves the canonical identity comparison. |
| `transition_composite` | Transitions respect pasting of **arbitrary** two squares, using canonical composite-pullback transports on both sides. |

The three additional private lemmas prove that composite-pullback and
equality-transport comparisons have the required conjugate mates; they are
proof infrastructure, not an exported API. For example, one can specialize
`adjoint_transition` to `Type v` or `AddCommGrpCat.{v}` and use
`transition_composite` with different stage maps in two consecutive squares.
All eleven named private clients in
[`SheafCohomologyExamples/SquareTransition.lean`](../SheafCohomologyExamples/SquareTransition.lean)
exercise these coefficient choices, the mate, target naturality,
proof-irrelevance, identity (including sheaves on the empty space), and
genuinely arbitrary two-square pasting. Use the focused
`import SheafCohomology.SquareTransition` or the aggregate
`import SheafCohomology`. The default example target imports these clients.

## Documentation and credit

This source-independent reference **supplements** the historical native API
rendering in [`API.md`](API.md); it is not a fresh doc-gen run or a claim that
the historical inventory includes this new module. The package uses its pinned
Lean `v4.34.0-rc2` and mathlib
`83abb3e776bdefcbc447a1e44d0debe4010039e5`; follow the repository
README's cache-first build instructions before compiling.

Original project contributors are credited as Formal Frontier Agents under
Apache-2.0. Anchor supplied the original source-local `Type` proof expressions
(commits `474d7f975dcc8560f4182a83f7b6bbe32cbf6762` and
`6daac54906b30cd4be04aff2ab15b1718eaed9ed`); Worker A adapted them to
the coefficient-generic incubator module, and Anchor assembled its accepted
revision `a2c6e8b61dcb5984c47e2af9e9c5203dffd4a88a`. This destination
transfer preserves its proofs and public signatures. This credit records
internal mathematical reuse, not source-level correspondence, a downstream
release, or a claim about an external human author. The full project credit and
license context remains in
[`CREDITS.md`](CREDITS.md) and [`LICENSE`](../LICENSE).
