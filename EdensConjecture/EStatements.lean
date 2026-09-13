import EdensConjecture.EStatementDefinitions
import EdensConjecture.MainProof.Torus
import EdensConjecture.MainProof.Refutations
import EdensConjecture.EmbeddedStrangeProof.Refutation

/-!
# Eden's conjecture: source-specific formulations and implications

## Sources

* Alp Eden, *An abstract theory of L-exponents with applications to dimension
  analysis*, Indiana University PhD thesis, 1989: II.2.1, II.4.6--4.8;
  III.1.1--1.3, III.1.27--1.28, III.1.37, III.3.1--3.4;
  IV.1, printed p.97; IV.2, Question 1, printed p.98.
* Wikipedia, "Eden's conjecture", opening paragraph, revision 1372866622:
  https://en.wikipedia.org/w/index.php?title=Eden%27s_conjecture&oldid=1372866622
* Wikipedia, "Lyapunov dimension", revision 1351052754: the linked
  dimension definitions and the supplementary noninteger-Hausdorff-dimension
  use of "strange attractor".
  https://en.wikipedia.org/w/index.php?title=Lyapunov_dimension&oldid=1351052754
* N. V. Kuznetsov and T. N. Mokaev, *A note on finite-time Lyapunov dimension
  of the Rossler attractor*, arXiv:1807.00235v1, section II, pp.1--2:
  https://arxiv.org/pdf/1807.00235v1
* N. V. Kuznetsov, *The Lyapunov dimension and its estimation via the Leonov
  method*, arXiv:1602.05410: discussion of non-interchangeable local-dimension
  constructions.
  https://arxiv.org/pdf/1602.05410

## Source correspondence

`EdensConjectureNeedNotUnstable` is the global supremum-attainment reading
with no instability requirement, expressed using the thesis's Hilbert-space
framework, cumulative local exponents and globally fixed index N. The thesis
supplies these definitions and the stationary/periodic terminology. Its
Question 1 does not literally assert this supremum-attainment proposition.

The modern global and embedded-strange statements both use the finite-time
construction. Local values take a time liminf at the candidate; set values
first take the spatial supremum and then a time liminf. No interchange of
these operations is assumed. The embedded-strange statement retains the
noninteger-Hausdorff-dimension and uniform-neighborhood conventions.

`EdensConjectureQuestion1` is the existential dimension-bound reading of the
thesis's Question 1: a critical path can be chosen stationary or periodic.
Here "critical" means d_L(u0) >= d_DO, as on printed p.97. It does not mean
that every critical path is stationary or periodic, nor that a path maximizes
at every finite time. The universal/existential quantifiers are an explicit
formal interpretation of a question rather than a verbatim theorem statement.

## Formal status

The thesis declarations retain their source-specific definitions. All modern
statements use the finite-time dimension convention.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped BigOperators Topology

namespace Eden

/-! ## Global supremum attainment with the thesis's definitions -/

universe u

/-- Global supremum attainment without an instability requirement.

The terminology and dimension formula follow Eden's thesis: s-numbers,
limsup of logarithmic exterior-volume growth, and the SAME N at every point
of X. A pointwise Kaplan--Yorke index is not substituted. The compact invariant
set is additionally required here to be a global attractor, preserving the
scope of this supremum-attainment reading.

This is not the exact question printed on p.98. For that question's
existential dimension-bound interpretation see `EdensConjectureQuestion1`.

IMPLICATION: on the same data, this conclusion implies that a stationary or
periodic critical path can be chosen, provided at least one critical path
exists. It is a weaker attainment conclusion than imposing instability on
periodic solutions, but this syntactic comparison alone does not identify
it with a declaration using a different local-dimension formula. -/
def EdensConjectureNeedNotUnstable : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] [SeparableSpace H],
    ∀ D : ThesisSetting H, D.IsGlobalAttractor →
      ∀ (N : ℕ) (μ : ℕ → H → ℝ),
        D.RealLocalSpectrumThrough N μ →
        D.FirstDimensionIndex N μ →
        (∀ u0 ∈ D.X, μ (N + 1) u0 < 0) →
        D.StationaryOrPeriodicSupremumAttainment N μ

theorem EdensConjectureNeedNotUnstable_False :
    ¬ EdensConjectureNeedNotUnstable.{u} := by
  exact PolynomialCounterexample.thesis_global_refutation

/-! ## Global attainment with the finite-time dimension -/

/-- Global attainment using the finite-time set dimension from Wikipedia's
linked dimension article. Both the local candidate and the set use finite-time dimensions.
The local value is their time liminf at the candidate.
The set value takes the spatial supremum before the time liminf. -/
def EdensConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ K : Set (PhaseSpace n), D.GlobalAttractor K →
      ∃ u0 ∈ K,
        (StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
        Orbit D.φ u0 ⊆ K ∧
        localLyapunovDimension D u0 = lyapunovDimension D K

/-- Refutation using a uniform finite-time lower bound on the global set
dimension and a smaller dimension at every stationary or periodic candidate. -/
theorem EdensConjecture_False : ¬ EdensConjecture := by
  exact PolynomialCounterexample.modern_refutation

/-! ## Embedded strange-attractor formulation in the Rössler note -/

/-- Section II of Kuznetsov--Mokaev, arXiv:1807.00235v1: supremum attainment
on a stationary point or an unstable periodic orbit embedded in a strange
attractor. This is the general conjecture paragraph, not a theorem restricted
to one numerical choice of parameters in the Rössler equations.

The strange-attractor qualifier is retained. The main formalization uses the
explicitly supplementary noninteger-Hausdorff-dimension convention above;
the 2018 paper does not supply that definition. No global-attractor or
"typical system" hypothesis is inserted, and no finite-time quantifier is
added to the conjecture sentence.

IMPLICATION: this assertion implies the same conclusion for strange GLOBAL
attractors. It does not by restriction imply a conclusion for non-strange
global attractors. Conversely, the global assertion alone supplies no
restriction argument covering all LOCAL strange attractors. -/
def EdensConjectureEmbeddedStrange : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ A : Set (PhaseSpace n),
      D.StrangeAttractorNonintegerHausdorff A →
        ∃ u0 ∈ A,
          (StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
          Orbit D.φ u0 ⊆ A ∧
          localLyapunovDimension D u0 = lyapunovDimension D A

theorem EdensConjectureEmbeddedStrange_False :
    ¬ EdensConjectureEmbeddedStrange := by
  exact StrangeProof.embeddedStrange_refutation

/-! ## Question 1 in Eden's thesis -/

/-- Existential dimension-bound reading of IV.2, Question 1, printed p.98.

"Is there an independent way of showing the critical path is a stationary
solution or a periodic solution?"

The critical-path predicate is the dimension-bound use on printed p.97:
d_L(u0) >= d_DO. Both this comparison and the thesis's Hausdorff-dimension
bounds are NON-STRICT. No supremum-attainment condition, instability
requirement, or common finite-time-maximizer condition is inserted.

The existential reading asks whether one such path can be CHOSEN; it does
not assert that ALL critical paths are stationary or periodic. The explicit
existence antecedent avoids importing the critical-path existence theorem
as an axiom. The compact invariant set need not be a global attractor.

IMPLICATION: with the same setting and local-dimension function, stationary
or periodic supremum attainment yields this conclusion whenever a critical
path exists. The named global-attainment declaration supplies that argument
only for settings whose X is a global attractor. -/
def EdensConjectureQuestion1 : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
      [CompleteSpace H] [SeparableSpace H],
    ∀ D : ThesisSetting H,
      ∀ (N : ℕ) (μ : ℕ → H → ℝ),
        D.RealLocalSpectrumThrough N μ →
        D.FirstDimensionIndex N μ →
        (∀ u0 ∈ D.X, μ (N + 1) u0 < 0) →
        (∃ u0 : H, D.CriticalPath N μ u0) →
        ∃ u0 : H, D.CriticalPath N μ u0 ∧
          (StationarySolution D.S u0 ∨ PeriodicSolution D.S u0)

theorem EdensConjectureQuestion1_False :
    ¬ EdensConjectureQuestion1.{u} := by
  exact PolynomialCounterexample.thesis_question1_refutation

end Eden
