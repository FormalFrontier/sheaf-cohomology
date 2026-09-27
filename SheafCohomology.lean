/-
Authors: Formal Frontier Agents
SPDX-License-Identifier: Apache-2.0
-/
module
public import SheafCohomology.FlasqueAcyclicResolution
public import SheafCohomology.FlasqueAcyclicSections
public import SheafCohomology.LocalCohomology
public import SheafCohomology.OpenCohomology
public import SheafCohomology.OpenCohomologyRightDerived
public import SheafCohomology.PullbackCoherence
public import SheafCohomology.PullbackLocalSections
public import SheafCohomology.NativeStageSectionEquality
public import SheafCohomology.NativeStageSectionLifting
public import SheafCohomology.ConePullback
public import SheafCohomology.ConePullbackSections
public import SheafCohomology.ConePullbackCocone
public import SheafCohomology.ConeOfPullbackCocone
public import SheafCohomology.ConePullbackLimit
public import SheafCohomology.ConePullbackLimitConverse
public import SheafCohomology.LimitConstruction
public import SheafCohomology.LimitPreservation
public import SheafCohomology.DiagramPushforward
public import SheafCohomology.SquareTransition
public import SheafCohomology.AbelianForget.Pullback
public import SheafCohomology.AbelianForget.FilteredColimits
public import SheafCohomology.AbelianForget.SquareTransition
public import SheafCohomology.AbelianForget.SheafedSpace
public import SheafCohomology.AbelianForget.ConePullback
public import SheafCohomology.AbelianForget.ConePullbackCocone
public import SheafCohomology.AbelianForget.DiagramPushforward
public import SheafCohomology.AbelianForget.LimitPreservation
public import SheafCohomology.OpenBaseChange
public import SheafCohomology.FilteredColimitFunctorH
public import SheafCohomology.HigherDirectImageFilteredColimit
public import SheafCohomology.CompactOpenSections
public import SheafCohomology.DegreeZero
public import SheafCohomology.FlasqueResolution
public import SheafCohomology.QuasiFlasque
public import SheafCohomology.QuasiFlasqueAcyclicity
public import SheafCohomology.QuasiFlasqueExactness

/-!
# Sheaf cohomology

Public entry point for compact-open sections, Ext and flasque resolutions,
local and open cohomology, filtered colimits, abelian-sheaf forgetful comparisons,
native inverse-image stalks and local sections, eventual native stage-section
equality and whole-stage section lifting over spectral limits, sheafed-space
cones and their section-unit transport,
a conditional native-limit criterion and its
fixed-base converse, actual limit
construction from coefficient colimits, native-to-space limit preservation, and
additive-to-Type forgetting with same-universe cofiltered-limit preservation,
commuting-square transitions, and open base change.
-/
