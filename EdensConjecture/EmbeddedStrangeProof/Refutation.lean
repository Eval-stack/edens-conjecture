import EdensConjecture.EStatementDefinitions
import EdensConjecture.EmbeddedStrangeProof.Aperiodicity
import EdensConjecture.EmbeddedStrangeProof.Geometry
import EdensConjecture.EmbeddedStrangeProof.Regularity
import EdensConjecture.EmbeddedStrangeProof.CantorMap
import EdensConjecture.EmbeddedStrangeProof.Dimension
import EdensConjecture.EmbeddedStrangeProof.NegativeFlow
import EdensConjecture.EmbeddedStrangeProof.DimensionUpper
import EdensConjecture.EmbeddedStrangeProof.EuclideanAttraction
import EdensConjecture.EmbeddedStrangeProof.ScalarRegularity
import EdensConjecture.EmbeddedStrangeProof.FlowSemigroup
import EdensConjecture.EmbeddedStrangeProof.EuclideanODE
import EdensConjecture.EmbeddedStrangeProof.FlowContinuity
import EdensConjecture.EmbeddedStrangeProof.FlowInverse
import EdensConjecture.EmbeddedStrangeProof.Removable
import EdensConjecture.EmbeddedStrangeProof.FlowRegularity

/-!
# Direct four-dimensional Cantor-comb construction

Development following `Eden_Strange_Easier_Counterexample.md`.
The intended attractor has Hausdorff dimension between 16/5 and 23/6.
Its two angular coordinates rotate at irrationally related frequencies.
The statement's noninteger-dimension convention does not require transitivity.

The explicit flow satisfies the C1-system obligations. The concrete attractor
has uniform attraction, invariance, aperiodicity and the required Hausdorff
bounds. Derivative injectivity follows from a local inverse Lipschitz bound.
The construction refutes the exact imported embedded-strange assertion.
-/

noncomputable section
namespace Eden.StrangeProof
open Set

/-- Stationarity entails a return at time one. -/
theorem not_stationary_of_noPositiveReturns
    {X : Type*} {S : ℝ → X → X} {A : Set X}
    (hfree : NoPositiveReturns S A) {p : X} (hp : p ∈ A) :
    ¬ Eden.StationarySolution S p := by
  intro hstationary
  exact hfree p hp 1 (by norm_num) (hstationary 1 (by norm_num))

/-- The imported definition of periodicity gives a return by setting the
initial time to zero. The identity at time zero is retained explicitly. -/
theorem not_periodic_of_noPositiveReturns
    {X : Type*} {S : ℝ → X → X} {A : Set X}
    (hinitial : ∀ p ∈ A, S 0 p = p)
    (hfree : NoPositiveReturns S A) {p : X} (hp : p ∈ A) :
    ¬ Eden.PeriodicSolution S p := by
  intro hperiodic
  rcases hperiodic.2 with ⟨T, hT, hperiod⟩
  have hreturn : S T p = p := by
    simpa only [zero_add, hinitial p hp] using hperiod 0 (le_refl 0)
  exact hfree p hp T hT hreturn


/-! ## The exact imported conjecture -/

/-- A strange attractor with no positive returns refutes the conjecture.
No calculation, replacement, or regularity assumption on local Lyapunov
dimension is needed: the trajectory alternative in the conclusion already
has no witness. -/
theorem not_EdenConjectureEmbeddedStrange_of_noPositiveReturns
    {n : ℕ} (hn : 0 < n) (D : Eden.C1DynamicalSystem n)
    (A : Set (Eden.PhaseSpace n))
    (hA : D.StrangeAttractorNonintegerHausdorff A)
    (hfree : NoPositiveReturns D.φ A) :
    ¬ (∀ n : ℕ, 0 < n → ∀ D : Eden.C1DynamicalSystem n,
      ∀ A : Set (Eden.PhaseSpace n), D.StrangeAttractorNonintegerHausdorff A →
        ∃ u0 ∈ A,
          (Eden.StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
          Eden.Orbit D.φ u0 ⊆ A ∧
          Eden.localLyapunovDimension D u0 =
            Eden.lyapunovDimension D A) := by
  intro hconjecture
  rcases hconjecture n hn D A hA with
    ⟨p, hp, heligible, _horbit, _hdimension⟩
  have hAU : A ⊆ D.U := hA.1.1.2.2.1
  have hinitial : ∀ q ∈ A, D.φ 0 q = q := by
    intro q hq
    exact D.initial q (hAU hq)
  rcases heligible with hstationary | hunstable
  · exact not_stationary_of_noPositiveReturns hfree hp hstationary
  · exact not_periodic_of_noPositiveReturns hinitial hfree hp hunstable.1

/-- The rational bounds in the direct construction rule out integer dimension. -/
theorem noninteger_dimH_of_bounds {A : Set (Eden.PhaseSpace 4)}
    (hlo : (16 : ENNReal) / 5 ≤ dimH A)
    (hhi : dimH A ≤ (23 : ENNReal) / 6) :
    ¬ ∃ m : ℕ, dimH A = (m : ENNReal) := by
  rintro ⟨m, hm⟩
  have h3 : (3 : ENNReal) < dimH A := lt_of_lt_of_le (by
    rw [ENNReal.lt_div_iff_mul_lt (by simp) (by simp)]
    norm_num) hlo
  have h4 : dimH A < (4 : ENNReal) := lt_of_le_of_lt hhi (by
    rw [ENNReal.div_lt_iff (by simp) (by simp)]
    norm_num)
  rw [hm] at h3 h4
  have h3m : 3 < m := by exact_mod_cast h3
  have hm4 : m < 4 := by exact_mod_cast h4
  omega

theorem directAttractor_noninteger_dimH :
    ¬ ∃ m : ℕ, dimH Direct.directAttractor = (m : ENNReal) :=
  noninteger_dimH_of_bounds Direct.directAttractor_dimH_lower Direct.directAttractor_dimH_upper

/-- Final logical step. The concrete flow, attraction, dimension bounds, and
no-return property must each be proved before this theorem closes the target. -/
theorem refutation_of_direct_construction
    (D : Eden.C1DynamicalSystem 4) (A : Set (Eden.PhaseSpace 4))
    (hattr : D.Attractor A)
    (hlo : (16 : ENNReal) / 5 ≤ dimH A)
    (hhi : dimH A ≤ (23 : ENNReal) / 6)
    (hfree : NoPositiveReturns D.φ A) :
    ¬ (∀ n : ℕ, 0 < n → ∀ D : Eden.C1DynamicalSystem n,
      ∀ A : Set (Eden.PhaseSpace n), D.StrangeAttractorNonintegerHausdorff A →
        ∃ u0 ∈ A,
          (Eden.StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
          Eden.Orbit D.φ u0 ⊆ A ∧
          Eden.localLyapunovDimension D u0 =
            Eden.lyapunovDimension D A) := by
  exact not_EdenConjectureEmbeddedStrange_of_noPositiveReturns (by decide) D A
    ⟨hattr, noninteger_dimH_of_bounds hlo hhi⟩ hfree

namespace Direct

def directSystem : Eden.C1DynamicalSystem 4 where
  U := phaseDomain
  open_U := isOpen_phaseDomain
  nonempty_U := phaseDomain_nonempty
  f := directField
  f_C1 := contDiffOn_directField
  φ := directFlow
  initial := fun _ hu => directFlow_zero hu
  forward_invariant := fun _ ht => directFlow_forward_invariant ht
  semigroup := fun _ _ ht hs _ hu => directFlow_semigroup hs ht hu
  continuous_flow := continuousOn_directFlow
  flow_C1 := fun _ ht => contDiffOn_directFlow ht
  solves_ODE := fun _ hu _ ht => (hasDerivAt_directFlow hu ht).hasDerivWithinAt
  derivative_injective := fun _ ht => directFlow_derivative_injective ht.le

theorem directSystem_attractor : directSystem.Attractor directAttractor := by
  refine ⟨⟨directAttractor_nonempty, isCompact_directAttractor,
    directAttractor_subset_phaseDomain, fun t _ => directFlow_image_attractor t⟩,
    phaseDomain, isOpen_phaseDomain, directAttractor_subset_phaseDomain, Subset.rfl, ?_⟩
  intro B hB _ ε hε
  obtain ⟨T, hT, hb⟩ := directFlow_uniform_attraction ε hε
  exact ⟨T, hT, fun t ht u hu => hb t ht u (hB hu)⟩

end Direct

theorem embeddedStrange_refutation :
    ¬ (∀ n : ℕ, 0 < n → ∀ D : Eden.C1DynamicalSystem n,
      ∀ A : Set (Eden.PhaseSpace n), D.StrangeAttractorNonintegerHausdorff A →
        ∃ u0 ∈ A,
          (Eden.StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
          Eden.Orbit D.φ u0 ⊆ A ∧
          Eden.localLyapunovDimension D u0 =
            Eden.lyapunovDimension D A) := by
  apply refutation_of_direct_construction Direct.directSystem Direct.directAttractor
    Direct.directSystem_attractor Direct.directAttractor_dimH_lower Direct.directAttractor_dimH_upper
  intro p hp t ht
  exact Direct.directFlow_no_positive_return hp ht

end Eden.StrangeProof

#print axioms Eden.StrangeProof.refutation_of_direct_construction
#print axioms Eden.StrangeProof.embeddedStrange_refutation
