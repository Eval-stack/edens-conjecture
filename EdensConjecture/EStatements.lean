import EdensConjecture.EStatementDefinitions
import EdensConjecture.DefinitionCheck
import EdensConjecture.EmbeddedStrangeProof.Refutation

/-!
# Eden's conjecture with the canonical local Lyapunov dimension

The updated manuscript, Definition 9 and Conjecture 11, uses finite-dimensional
systems and the infimum of orders with strictly negative upper exponential
singular-value growth. Every statement below uses that same local dimension.
The main statement requires an unstable periodic orbit, as requested.

The global target is the spatial supremum of the canonical local dimensions.
It is not identified by definition with the infimum of finite-time set dimensions.
The embedded-strange variant retains the noninteger Hausdorff-dimension convention.

`DefinitionCheck` proves agreement of the three dimension constructions under
finite real convergence of every singular-value growth rate and verifies that
condition throughout the polynomial global attractor. The global and critical-path
refutations use that agreement. The embedded-strange refutation excludes stationary
and periodic points independently of the dimension formula.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped BigOperators Topology

namespace Eden

/-- Global Eden conjecture: the supremum of canonical local dimensions on a
global attractor is attained at a stationary point or an unstable periodic orbit.
This uses the manuscript's supremum target with the requested instability condition. -/
def EdensConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ K : Set (PhaseSpace n), D.GlobalAttractor K →
      ∃ u0 ∈ K,
        (StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
        Orbit D.φ u0 ⊆ K ∧
        localLyapunovDimension D u0 = supremumLocalLyapunovDimension D K

/-- The global variant allowing any nonstationary periodic orbit.
The system, local dimension and supremum target are the same as above. -/
def EdensConjectureNeedNotUnstable : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ K : Set (PhaseSpace n), D.GlobalAttractor K →
      ∃ u0 ∈ K,
        (StationarySolution D.φ u0 ∨ PeriodicSolution D.φ u0) ∧
        Orbit D.φ u0 ⊆ K ∧
        localLyapunovDimension D u0 = supremumLocalLyapunovDimension D K

theorem EdensConjectureNeedNotUnstable_False : ¬ EdensConjectureNeedNotUnstable := by
  exact DefinitionCheck.Counterexample.global_refutation

theorem EdensConjecture_False : ¬ EdensConjecture := by
  intro h
  apply EdensConjectureNeedNotUnstable_False
  intro n hn D K hK
  obtain ⟨p, hp, hs | hu, horbit, hdim⟩ := h n hn D K hK
  · exact ⟨p, hp, Or.inl hs, horbit, hdim⟩
  · exact ⟨p, hp, Or.inr hu.1, horbit, hdim⟩

/-- Supremum attainment at a stationary point or an unstable periodic orbit
embedded in a strange local attractor, using the canonical local dimension. -/
def EdensConjectureEmbeddedStrange : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ A : Set (PhaseSpace n),
      D.StrangeAttractorNonintegerHausdorff A →
        ∃ u0 ∈ A,
          (StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
          Orbit D.φ u0 ⊆ A ∧
          localLyapunovDimension D u0 = supremumLocalLyapunovDimension D A

theorem EdensConjectureEmbeddedStrange_False :
    ¬ EdensConjectureEmbeddedStrange := by
  exact StrangeProof.embeddedStrange_refutation

/-- Finite-dimensional critical-path variant of Question 1: if a compact
invariant set has a critical point, it has a stationary or periodic critical
point. Both occurrences of `CriticalPath` use the canonical local dimension. -/
def EdensConjectureQuestion1 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ K : Set (PhaseSpace n), D.CompactInvariantSet K →
      (∃ u0 : PhaseSpace n, CriticalPath D K u0) →
      ∃ u0 : PhaseSpace n, CriticalPath D K u0 ∧
        (StationarySolution D.φ u0 ∨ PeriodicSolution D.φ u0)

theorem EdensConjectureQuestion1_False : ¬ EdensConjectureQuestion1 := by
  exact DefinitionCheck.Counterexample.question1_refutation

end Eden
