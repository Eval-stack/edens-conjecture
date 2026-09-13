import EdensConjecture.EStatementDefinitions
import EdensConjecture.EMainProof

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
* N. V. Kuznetsov, T. A. Alexeeva and G. A. Leonov, *Invariance of Lyapunov
  exponents and Lyapunov dimension for regular and irregular linearizations*,
  arXiv:1410.2016v3, section 2 and Corollary 2: the pointwise Kaplan--Yorke
  dimension formed from upper singular-value Lyapunov exponents.
  https://arxiv.org/html/1410.2016v3
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

`EdensConjecture` retains Wikipedia's global-attractor scope, attainment of
the supremum, and stationary-point-or-unstable-periodic-orbit alternative.
It is a continuous-time finite-dimensional formalization using the
Kaplan--Yorke dimension of upper singular-value Lyapunov exponents,
not a formalization of all PDE settings.

`EdensConjectureEmbeddedStrange` retains the strange-attractor qualification
and the embedded stationary/unstable-periodic alternative in section II of
the Rössler note. Global attraction is not inserted. The paper does not
mathematically define "strange attractor" or uniquely specify an infinite-time
pointwise local-dimension convention in that conjecture paragraph. The
same exponent-based pointwise convention is fixed for both modern
formulations below. The noninteger-Hausdorff-dimension interpretation and
the uniform-neighborhood attraction convention are explicit supplements,
not definitions attributed
to that paper. Its equations (5)--(6) concern finite-time dimensions; they do
not by themselves license adding "for every positive time" to the conjecture.

`EdensConjectureQuestion1` is the existential dimension-bound reading of the
thesis's Question 1: a critical path can be chosen stationary or periodic.
Here "critical" means d_L(u0) >= d_DO, as on printed p.97. It does not mean
that every critical path is stationary or periodic, nor that a path maximizes
at every finite time. The universal/existential quantifiers are an explicit
formal interpretation of a question rather than a verbatim theorem statement.

## Formal status

The four declarations ending in `_False` are direct-negation targets with
unproved bodies. Their names do not assert that a refutation has been verified.
No support definition uses an admitted body. The thesis ratio is restricted
explicitly to finite real exponents through N+1; no convention for an
indeterminate extended-real ratio is added. This file has not been checked
by a Lean compiler.
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

/-! ## Wikipedia's global-attractor formulation -/

/-- Wikipedia's opening formulation, in the continuous-time finite-dimensional
setting, using the fixed exponent-based local Lyapunov dimension above.

The attaining point must be stationary or lie on an UNSTABLE periodic orbit.
Membership in K and inclusion of the orbit in K express embeddedness. The
orbit-inclusion condition is also a consequence of invariance and membership.
No genericity or strange-attractor qualification is added.

IMPLICATION: deleting the instability requirement weakens the conclusion on
these same data. Restricting the quantified attractors to those that are also
strange weakens the universal assertion. Neither observation supplies a
comparison with a different dimension convention or a different system class. -/
def EdensConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
    ∀ K : Set (PhaseSpace n), D.GlobalAttractor K →
      ∃ u0 ∈ K,
        (StationarySolution D.φ u0 ∨ D.UnstablePeriodicOrbit u0) ∧
        Orbit D.φ u0 ⊆ K ∧
        localLyapunovDimension D u0 =
          sSup (localLyapunovDimension D '' K)

theorem EdensConjecture_False :
    ¬ EdensConjecture := by
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
          localLyapunovDimension D u0 =
            sSup (localLyapunovDimension D '' A)

theorem EdensConjectureEmbeddedStrange_False :
    ¬ EdensConjectureEmbeddedStrange := by
  sorry

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
