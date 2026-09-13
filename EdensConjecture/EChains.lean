import EdensConjecture.EStatement

/-!
## Implications

On identical system, set and local-dimension data:

  stationary-or-unstable-periodic supremum attainment
    ==> stationary-or-periodic supremum attainment;

  stationary-or-periodic supremum attainment + existence of a critical path
    ==> existence of a stationary-or-periodic critical path.

Their contrapositives reverse the arrows. In particular, excluding all
periodic solutions is stronger than excluding only unstable periodic ones.
The elementary implications are proved below without using any `_False`
declaration.

With this fixed pointwise dimension, the global-attractor assertion and the
strange-attractor assertion each imply their restriction to sets that are
BOTH global and strange. Neither source's wording supplies an implication
in the reverse direction. The strange-attractor assertion also covers local
attractors, so it is not merely the global-attractor assertion with one extra
hypothesis.

The four named declarations do NOT form an unconditional linear hierarchy.
The thesis definitions use a fixed-index ratio of cumulative local exponents;
the modern definitions use pointwise Kaplan--Yorke constructions. The thesis
and modern declarations also quantify over different ambient settings.
Consequently, `EdensConjecture` does not imply the named thesis declaration
merely by deleting the word "unstable": a theorem identifying the relevant
settings and dimension functions would additionally be required.

Similarly, `EdensConjectureNeedNotUnstable` concerns global attractors whereas
`EdensConjectureQuestion1` retains the thesis's compact-invariant-set framework.
The former implies the conclusion of Question 1 ON GLOBAL ATTRACTORS, not the
full compact-invariant-set assertion solely by logic.

# Logical comparisons between Eden conjecture formulations

The proofs in this file use only the positive conjecture hypotheses and the
defining predicates. In particular, none invokes an admitted negation.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped BigOperators Topology

namespace Eden

universe u

/-- Instability is an extra requirement, not an alternative definition of a
periodic solution. Removing it is a logically valid relaxation. -/
theorem stationaryOrUnstablePeriodic_implies_stationaryOrPeriodic
    {n : ℕ} (D : C1DynamicalSystem n) (p : PhaseSpace n)
    (h : StationarySolution D.φ p ∨ D.UnstablePeriodicOrbit p) :
    StationarySolution D.φ p ∨ PeriodicSolution D.φ p := by
  rcases h with hs | hp
  · exact Or.inl hs
  · exact Or.inr hp.1

/-- The Wikipedia-form assertion implies attainment without an instability
requirement on the SAME finite-dimensional data and SAME convention.
This is not a cross-definition identification with the thesis formula. -/
theorem EdensConjecture_implies_periodicAttainment
    (h : EdensConjecture)
    {n : ℕ} (hn : 0 < n) (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (hK : D.GlobalAttractor K) :
    ∃ p ∈ K,
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) ∧
      Orbit D.φ p ⊆ K ∧
      localLyapunovDimension D p =
        sSup (localLyapunovDimension D '' K) := by
  rcases h n hn D K hK with ⟨p, hp, heligible, horbit, hdim⟩
  exact ⟨p, hp,
    stationaryOrUnstablePeriodic_implies_stationaryOrPeriodic D p heligible,
    horbit, hdim⟩

/-- Contrapositive on identical finite-dimensional data: excluding all
stationary and periodic maximizers refutes the Wikipedia-form assertion.
No converse is inferred. -/
theorem noPeriodicAttainment_implies_not_EdensConjecture
    {n : ℕ} (hn : 0 < n) (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (hK : D.GlobalAttractor K)
    (hgap : ¬ ∃ p ∈ K,
      (StationarySolution D.φ p ∨ PeriodicSolution D.φ p) ∧
      Orbit D.φ p ⊆ K ∧
      localLyapunovDimension D p =
        sSup (localLyapunovDimension D '' K)) :
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
          localLyapunovDimension D p =
            sSup (localLyapunovDimension D '' X)

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
