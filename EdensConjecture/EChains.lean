import EdensConjecture.EStatements

/-!
# Implications between the revised Eden conjectures

All attainment statements use the canonical local dimension and its spatial
supremum. The critical-path comparison is stated explicitly where needed.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped BigOperators Topology

namespace Eden

/-- Removing instability preserves stationary/periodic eligibility. -/
theorem stationaryOrUnstablePeriodic_implies_stationaryOrPeriodic
    {n : ℕ} (D : C1DynamicalSystem n) (p : PhaseSpace n)
    (h : StationarySolution D.φ p ∨ D.UnstablePeriodicOrbit p) :
    StationarySolution D.φ p ∨ PeriodicSolution D.φ p := by
  rcases h with hs | hp
  · exact Or.inl hs
  · exact Or.inr hp.1

/-- The instability version implies the variant allowing any periodic orbit. -/
theorem EdensConjecture_implies_needNotUnstable :
    EdensConjecture → EdensConjectureNeedNotUnstable := by
  intro h n hn D K hK
  rcases h n hn D K hK with ⟨p, hp, heligible, horbit, hdim⟩
  exact ⟨p, hp,
    stationaryOrUnstablePeriodic_implies_stationaryOrPeriodic D p heligible,
    horbit, hdim⟩

theorem EdensConjecture_implies_periodicAttainment
    (h : EdensConjecture)
    {n : ℕ} (hn : 0 < n) (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (hK : D.GlobalAttractor K) :
    ∃ p ∈ K,
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) ∧
      Orbit D.φ p ⊆ K ∧
      localLyapunovDimension D p = supremumLocalLyapunovDimension D K := by
  exact EdensConjecture_implies_needNotUnstable h _ hn D K hK

/-- Excluding all stationary and periodic maximizers refutes the conjecture. -/
theorem noPeriodicAttainment_implies_not_EdensConjecture
    {n : ℕ} (hn : 0 < n) (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (hK : D.GlobalAttractor K)
    (hgap : ¬ ∃ p ∈ K,
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) ∧
      Orbit D.φ p ⊆ K ∧
      localLyapunovDimension D p = supremumLocalLyapunovDimension D K) :
    ¬ EdensConjecture := by
  intro h
  exact hgap (EdensConjecture_implies_periodicAttainment h hn D K hK)

/-- Restriction to attractors which are both global and strange. -/
def AttainmentOnGlobalStrangeAttractors : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ K : Set (PhaseSpace n), D.GlobalAttractor K →
      D.StrangeAttractorNonintegerHausdorff K →
        ∃ p ∈ K,
          (StationarySolution D.φ p ∨ D.UnstablePeriodicOrbit p) ∧
          Orbit D.φ p ⊆ K ∧
          localLyapunovDimension D p = supremumLocalLyapunovDimension D K

theorem EdensConjecture_implies_globalStrangeRestriction :
    EdensConjecture → AttainmentOnGlobalStrangeAttractors := by
  intro h n hn D K hglobal _hstrange
  exact h n hn D K hglobal

theorem EdensConjectureEmbeddedStrange_implies_globalStrangeRestriction :
    EdensConjectureEmbeddedStrange → AttainmentOnGlobalStrangeAttractors := by
  intro h n hn D K _hglobal hstrange
  exact h n hn D K hstrange

/-- An attaining stationary/periodic point is critical whenever any critical
point exists. EReal makes the supremum comparison valid even at +∞. -/
theorem supremumAttainment_implies_stationaryOrPeriodicCriticalPath
    {n : ℕ} (D : C1DynamicalSystem n) (K : Set (PhaseSpace n))
    (hmax : ∃ p ∈ K,
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) ∧
      localLyapunovDimension D p = supremumLocalLyapunovDimension D K)
    (hcrit : ∃ q : PhaseSpace n, CriticalPath D K q) :
    ∃ p : PhaseSpace n, CriticalPath D K p ∧
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) := by
  rcases hmax with ⟨p, hp, horbit, heq⟩
  rcases hcrit with ⟨q, hqK, hqbound⟩
  have hqle : localLyapunovDimension D q ≤ supremumLocalLyapunovDimension D K :=
    le_sSup (Set.mem_image_of_mem _ hqK)
  refine ⟨p, ⟨hp, ?_⟩, horbit⟩
  rw [heq]
  exact hqbound.trans hqle

theorem EdensConjectureNeedNotUnstable_implies_question1_onGlobalAttractor
    (h : EdensConjectureNeedNotUnstable)
    {n : ℕ} (hn : 0 < n) (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (hglobal : D.GlobalAttractor K)
    (hexists : ∃ p : PhaseSpace n, CriticalPath D K p) :
    ∃ p : PhaseSpace n, CriticalPath D K p ∧
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) := by
  rcases h n hn D K hglobal with ⟨p, hp, horbit, _, hdim⟩
  exact supremumAttainment_implies_stationaryOrPeriodicCriticalPath D K
    ⟨p, hp, horbit, hdim⟩ hexists

end Eden
