/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
import SheafCohomology
import SheafCohomologyExamples.AbelianForgetPullback
import SheafCohomologyExamples.AbelianForgetFilteredColimits
import SheafCohomologyExamples.SquareTransition
import SheafCohomologyExamples.AbelianForgetSquareTransition
import SheafCohomologyExamples.ConePullback
import SheafCohomologyExamples.ConePullbackSections
import SheafCohomologyExamples.PullbackLocalSections
import SheafCohomologyExamples.NativeStageSectionEquality
import SheafCohomologyExamples.NativeStageSectionLifting
import SheafCohomologyExamples.NativeStageSectionColimit
import SheafCohomologyExamples.ConePullbackCocone
import SheafCohomologyExamples.ConeOfPullbackCocone
import SheafCohomologyExamples.ConePullbackLimit
import SheafCohomologyExamples.ConePullbackLimitConverse
import SheafCohomologyExamples.LimitConstruction
import SheafCohomologyExamples.LimitPreservation
import SheafCohomologyExamples.DiagramPushforward
import SheafCohomologyExamples.AbelianForgetSheafedSpace
import SheafCohomologyExamples.AbelianForgetConePullback
import SheafCohomologyExamples.AbelianForgetConePullbackCocone
import SheafCohomologyExamples.AbelianForgetDiagramPushforward
import SheafCohomologyExamples.AbelianForgetLimitPreservation

/-!
# Public-root sheaf cohomology examples

The clients defined here use only the aggregate public import. Imported client
modules also exercise focused public imports. The root's clients are private
and named; imported modules additionally include named public section-transport
clients. The local-pullback leaf additionally provides four named public clients
for actual-unit germs, local representation, equality neighborhoods and finite covers.
The native stage-equality leaf gives two public distinguishability clients.
The native stage-lifting leaf gives two private ordinary-import clients for
eventual native-section inhabitation and persistence along later arrows.
The native stage-colimit leaf gives two private ordinary-import clients for
cancellation and recovery of a target coprojection through the actual comparison.
Together they exercise
compact-open and degree-zero colimits, quasi-flasqueness, acyclic resolutions,
local cohomology, all-degree derived colimits, pullback and open base change,
including native sheafed-space cones, literal section units and restricted
triangle transport, the conditional native-limit criterion,
its fixed-base converse with actual native and underlying-space limits,
actual limit construction, genuine empty-index limits and native-to-space
limit preservation,
and additive-to-Type forgetting with same-universe cofiltered-limit preservation.
The flasque and derived-colimit examples retain their universe-zero boundaries.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace SheafCohomologyExamples

private theorem compactOpenColimitComparison
    {X : TopCat.{0}} [PrespectralSpace X] [QuasiSeparatedSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {I : Type} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0})
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    IsIso (colimit.post F (SheafCohomology.CompactOpenSections.sections U)) :=
  SheafCohomology.CompactOpenSections.canonicalSectionsComparison_isIso F U hU

private theorem degreeZeroFilteredColimit
    {X : TopCat.{0}} [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasExt.{0} (X.Sheaf AddCommGrpCat.{0})]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{0}]
    {I : Type} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0}) :
    PreservesColimit F
      (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) 0) :=
  SheafCohomology.DegreeZero.preservesColimit_functorH_zero F

private theorem setValuedQuasiFlasqueCriterion
    {X : Type u} [TopologicalSpace X]
    (F : CategoryTheory.Sheaf
      (Opens.grothendieckTopology X) (Type u)) :
    TopCat.Sheaf.IsQuasiFlasque F ↔
      ∀ (U : Opens X) (_hU : IsCompact (U : Set X)),
        Function.Surjective ((TopCat.Sheaf.restriction U).app F) :=
  TopCat.Sheaf.IsQuasiFlasque.iff_surjective F

private theorem flasqueResolutionUnderlyingComplex
    {X : TopCat.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    [PrespectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasExt.{0} (X.Sheaf AddCommGrpCat.{0})]
    (F : X.Sheaf AddCommGrpCat.{0}) :
    (TopCat.Sheaf.flasqueAcyclicResolution F).cocomplex =
      TopCat.Sheaf.flasqueResolution F :=
  rfl

private noncomputable def flasqueExtSectionsHomologyIso
    {X : TopCat.{0}} [CompactSpace X] [QuasiSeparatedSpace X]
    [PrespectralSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasExt.{0} (X.Sheaf AddCommGrpCat.{0})]
    (F : X.Sheaf AddCommGrpCat.{0}) (q : ℕ) :
    (TopCat.Sheaf.flasqueAcyclicResolution F).extZeroComplex.homology q ≅
      (TopCat.Sheaf.flasqueResolutionSections F).homology q :=
  TopCat.Sheaf.flasqueAcyclicResolutionExtZeroHomologyIsoSectionsHomology F q

private theorem localCohomologyOnOpen
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    (F : X.Sheaf AddCommGrpCat.{u}) (q : ℕ) (U : Opens Y) :
    (TopCat.Sheaf.localCohomologyPresheaf f F q).obj (.op U) =
      CategoryTheory.Sheaf.H'
        (show CategoryTheory.Sheaf
          (Opens.grothendieckTopology X) AddCommGrpCat.{u} from F)
        q ((Opens.map f).obj U) :=
  TopCat.Sheaf.localCohomologyPresheaf_obj f F q U

private theorem localCohomologyCoefficientMap
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    (q : ℕ) {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G)
    (U : Opens Y) :
    ((TopCat.Sheaf.localCohomologyPresheafFunctor f q).map a).app (.op U) =
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) q).map a).app
          (.op ((Opens.map f).obj U)) :=
  TopCat.Sheaf.localCohomologyPresheafFunctor_map_app f q a U

private noncomputable def positiveLocalDerivedComparison
    {X Y : TopCat.{u}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    [HasExt.{u} (X.Sheaf AddCommGrpCat.{u})]
    (q : ℕ) (hq : 0 < q) :
    TopCat.Sheaf.sheafifiedLocalCohomologyFunctor f q ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived q :=
  TopCat.Sheaf.RightDerivedPushforward.sheafifiedLocalCohomologyFunctorIsoRightDerived
    f q hq

private theorem allDegreeDerivedColimit
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    [PrespectralSpace X] [QuasiSeparatedSpace X] [PrespectralSpace Y]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
    [HasExt.{0} (X.Sheaf AddCommGrpCat.{0})]
    {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0}) (hf : IsSpectralMap f) (q : ℕ) :
    IsIso (colimit.post F
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q)) :=
  SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_isIso
    f F hf q

private theorem allDegreeDerivedColimitStage
    {X Y : TopCat.{0}} (f : X ⟶ Y)
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{0}]
    [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{0}]
    {I : Type} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (F : I ⥤ X.Sheaf AddCommGrpCat.{0}) (q : ℕ) (i : I) :
    colimit.ι
        (F ⋙ (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) i ≫
      colimit.post F
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q) =
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).rightDerived q).map
      (colimit.ι F i) :=
  SheafCohomology.HigherDirectImageFilteredColimit.rightDerivedPushforward_colimitPost_ι
    f F q i

private noncomputable def pullbackCompositionComparison
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback (Type u) g ⋙ TopCat.Sheaf.pullback (Type u) f ≅
      TopCat.Sheaf.pullback (Type u) (f ≫ g) :=
  TopCat.Sheaf.pullbackCompIso (Type u) f g

private theorem openPullbackSquareCommutes
    {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens Y) :
    TopCat.Sheaf.OpenBaseChange.preimageMap f V ≫ V.inclusion' =
      ((Opens.map f).obj V).inclusion' ≫ f :=
  TopCat.Sheaf.OpenBaseChange.preimageMap_comp_inclusion f V

private noncomputable def openBaseChangeComparison
    {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens Y) :
    TopCat.Sheaf.pushforward (Type u) f ⋙
        TopCat.Sheaf.pullback (Type u) V.inclusion' ≅
      TopCat.Sheaf.pullback (Type u) ((Opens.map f).obj V).inclusion' ⋙
        TopCat.Sheaf.pushforward (Type u)
          (TopCat.Sheaf.OpenBaseChange.preimageMap f V) :=
  TopCat.Sheaf.OpenBaseChange.baseChangeIso f V

private theorem openBaseChangeMate
    {X Y : TopCat.{u}} (f : X ⟶ Y) (V : Opens Y) :
    CategoryTheory.mateEquiv
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (TopCat.Sheaf.OpenBaseChange.preimageMap f V))
      (TopCat.Sheaf.OpenBaseChange.pullbackSquare f V) =
        TopCat.Sheaf.OpenBaseChange.baseChangeSquare f V :=
  TopCat.Sheaf.OpenBaseChange.pullbackSquare_mate f V

#print axioms compactOpenColimitComparison
#print axioms degreeZeroFilteredColimit
#print axioms setValuedQuasiFlasqueCriterion
#print axioms flasqueResolutionUnderlyingComplex
#print axioms flasqueExtSectionsHomologyIso
#print axioms localCohomologyOnOpen
#print axioms localCohomologyCoefficientMap
#print axioms positiveLocalDerivedComparison
#print axioms allDegreeDerivedColimit
#print axioms allDegreeDerivedColimitStage
#print axioms pullbackCompositionComparison
#print axioms openPullbackSquareCommutes
#print axioms openBaseChangeComparison
#print axioms openBaseChangeMate

end SheafCohomologyExamples
