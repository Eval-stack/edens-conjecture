import EdensConjecture.EStatements

/-!
# Implications between the finite-time formulations

Global and embedded-strange attainment use the same finite-time local and
set dimensions. Each restricts to sets that are both global and strange.
The thesis declarations retain their original fixed-index dimensions; no
identification with the modern construction is assumed.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped BigOperators Topology

namespace Eden

universe u

namespace ThesisSetting

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (D : ThesisSetting H)

/-- One implication that needs no comparison between different definitions
of Lyapunov dimension: an attaining stationary/periodic solution is critical
whenever some critical path exists. All quantities refer to the same X, N,
mu and the same thesis local dimension.

Thus, on fixed data, supremum attainment is stronger than the existential
dimension-bound assertion. The converse is not supplied by the definitions. -/
theorem supremumAttainment_implies_stationaryOrPeriodicCriticalPath
    (N : ℕ) (μ : ℕ → H → ℝ)
    (hmax : D.StationaryOrPeriodicSupremumAttainment N μ)
    (hcrit : ∃ u : H, D.CriticalPath N μ u) :
    ∃ u : H, D.CriticalPath N μ u ∧
      (StationarySolution D.S u ∨ PeriodicSolution D.S u) := by
  rcases hmax with ⟨p, hp, horbit, heq⟩
  rcases hcrit with ⟨q, hqX, hqbound⟩
  have hqle : (D.localLyapunovDimension N μ q : EReal) ≤
      D.supremumLocalLyapunovDimension N μ := by
    unfold supremumLocalLyapunovDimension
    exact le_sSup ⟨q, hqX, rfl⟩
  have hbound : D.douadyOesterleDimension N ≤
      (D.localLyapunovDimension N μ p : EReal) := by
    rw [heq]
    exact le_trans hqbound hqle
  exact ⟨p, ⟨hp, hbound⟩, horbit⟩

end ThesisSetting

/-- Instability is an extra requirement, not an alternative definition of a
periodic solution. Removing it is a logically valid relaxation. -/
theorem stationaryOrUnstablePeriodic_implies_stationaryOrPeriodic
    {n : ℕ} (D : C1DynamicalSystem n) (p : PhaseSpace n)
    (h : StationarySolution D.φ p ∨ D.UnstablePeriodicOrbit p) :
    StationarySolution D.φ p ∨ PeriodicSolution D.φ p := by
  rcases h with hs | hp
  · exact Or.inl hs
  · exact Or.inr hp.1

/-- Removing the instability requirement preserves the finite-time set target. -/
theorem EdensConjecture_implies_periodicAttainment
    (h : EdensConjecture)
    {n : ℕ} (hn : 0 < n) (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (hK : D.GlobalAttractor K) :
    ∃ p ∈ K,
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) ∧
      Orbit D.φ p ⊆ K ∧
      localLyapunovDimension D p = lyapunovDimension D K := by
  rcases h n hn D K hK with ⟨p, hp, heligible, horbit, hdim⟩
  exact ⟨p, hp,
    stationaryOrUnstablePeriodic_implies_stationaryOrPeriodic D p heligible,
    horbit, hdim⟩

/-- Contrapositive on identical finite-dimensional data: excluding all
stationary and periodic maximizers refutes the finite-time assertion.
No converse is inferred. -/
theorem noPeriodicAttainment_implies_not_EdensConjecture
    {n : ℕ} (hn : 0 < n) (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (hK : D.GlobalAttractor K)
    (hgap : ¬ ∃ p ∈ K,
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) ∧
      Orbit D.φ p ⊆ K ∧
      localLyapunovDimension D p = lyapunovDimension D K) :
    ¬ EdensConjecture := by
  intro h
  exact hgap (EdensConjecture_implies_periodicAttainment h hn D K hK)

/-- Common restriction of the two modern formulations. Both antecedents are
shown explicitly: X is global AND strange. Neither is silently substituted
for the other. -/
def AttainmentOnGlobalStrangeAttractors : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ X : Set (PhaseSpace n), D.GlobalAttractor X →
      D.StrangeAttractorNonintegerHausdorff X →
        ∃ p ∈ X,
          (StationarySolution D.φ p ∨ D.UnstablePeriodicOrbit p) ∧
          Orbit D.φ p ⊆ X ∧
          localLyapunovDimension D p = lyapunovDimension D X

/-- The global assertion implies its global-and-strange restriction. -/
theorem EdensConjecture_implies_globalStrangeRestriction :
    EdensConjecture → AttainmentOnGlobalStrangeAttractors := by
  intro h n hn D X hglobal _hstrange
  exact h n hn D X hglobal

/-- The strange-attractor assertion also implies its global-and-strange
restriction. This does not give an arrow to all global attractors. -/
theorem EdensConjectureEmbeddedStrange_implies_globalStrangeRestriction :
    EdensConjectureEmbeddedStrange →
      AttainmentOnGlobalStrangeAttractors := by
  intro h n hn D X _hglobal hstrange
  exact h n hn D X hstrange

/-- On a global attractor in the thesis setting, the supremum-attainment
assertion supplies the existential conclusion of Question 1. The assumption
of globality is essential to this deduction from the named antecedent;
Question 1 itself is stated on the wider compact-invariant-set framework. -/
theorem EdensConjectureNeedNotUnstable_implies_question1_onGlobalAttractor
    (h : EdensConjectureNeedNotUnstable.{u})
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SeparableSpace H]
    (D : ThesisSetting H) (hglobal : D.IsGlobalAttractor)
    (N : ℕ) (μ : ℕ → H → ℝ)
    (hspectrum : D.RealLocalSpectrumThrough N μ)
    (hindex : D.FirstDimensionIndex N μ)
    (hnegative : ∀ p ∈ D.X, μ (N + 1) p < 0)
    (hexists : ∃ p : H, D.CriticalPath N μ p) :
    ∃ p : H, D.CriticalPath N μ p ∧
      (StationarySolution D.S p ∨ PeriodicSolution D.S p) := by
  have hmax : D.StationaryOrPeriodicSupremumAttainment N μ :=
    h H D hglobal N μ hspectrum hindex hnegative
  exact D.supremumAttainment_implies_stationaryOrPeriodicCriticalPath
    N μ hmax hexists

end Eden
