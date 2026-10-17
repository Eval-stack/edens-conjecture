import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

noncomputable section

open Set Filter TopologicalSpace
open scoped BigOperators Topology

namespace Eden

/-!
# Definitions

This file defines terminology used to state Eden's Conjecture and its variants in `EStatements.lean`. Additional proof-specific definitions are in the `MainProof` folder.
-/

/-! ## Elementary trajectory terminology -/

def StationarySolution {H : Type*} (S : ℝ → H → H) (u0 : H) : Prop :=
  ∀ t : ℝ, 0 ≤ t → S t u0 = u0

/-- Nonstationary periodic solution. Stationary solutions are allowed separately
in every conjecture below, so excluding them here changes no conclusion. -/
def PeriodicSolution {H : Type*} (S : ℝ → H → H) (u0 : H) : Prop :=
  ¬ StationarySolution S u0 ∧
    ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, 0 ≤ t → S (t + T) u0 = S t u0


def Orbit {H : Type*} (S : ℝ → H → H) (u0 : H) : Set H :=
  {u | ∃ t : ℝ, 0 ≤ t ∧ S t u0 = u}

/-! ## Continuous-time finite-dimensional systems -/

abbrev PhaseSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A C1 autonomous differential equation and its forward solution operator
on an open, forward-invariant phase domain. Values outside the domain or at
negative times are not used in the statements. -/
structure C1DynamicalSystem (n : ℕ) where
  U : Set (PhaseSpace n)
  open_U : IsOpen U
  nonempty_U : U.Nonempty
  f : PhaseSpace n → PhaseSpace n
  f_C1 : ContDiffOn ℝ 1 f U
  φ : ℝ → PhaseSpace n → PhaseSpace n
  initial : ∀ u ∈ U, φ 0 u = u
  forward_invariant : ∀ t : ℝ, 0 ≤ t → MapsTo (φ t) U U
  semigroup : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    ∀ u ∈ U, φ (t + s) u = φ t (φ s u)
  continuous_flow :
    ContinuousOn (fun p : ℝ × PhaseSpace n => φ p.1 p.2)
      ((Ici 0) ×ˢ U)
  flow_C1 : ∀ t : ℝ, 0 ≤ t → ContDiffOn ℝ 1 (φ t) U
  solves_ODE : ∀ u ∈ U, ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s : ℝ => φ s u) (f (φ t u)) (Ici 0) t
  derivative_injective : ∀ t : ℝ, 0 < t → ∀ u ∈ U,
    Function.Injective (fderiv ℝ (φ t) u)

namespace C1DynamicalSystem

variable {n : ℕ} (D : C1DynamicalSystem n)

/-- Uniform attraction, with its quantifiers written explicitly. -/
def UniformlyAttracts (K B : Set (PhaseSpace n)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → ∀ u ∈ B,
        ∃ v ∈ K, dist (D.φ t u) v < ε


def CompactInvariantSet (K : Set (PhaseSpace n)) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ K ⊆ D.U ∧
    ∀ t : ℝ, 0 ≤ t → D.φ t '' K = K

/-- Compact invariant set attracting every bounded subset of the phase domain. -/
def GlobalAttractor (K : Set (PhaseSpace n)) : Prop :=
  D.CompactInvariantSet K ∧
    ∀ B : Set (PhaseSpace n), B ⊆ D.U → Bornology.IsBounded B →
      D.UniformlyAttracts K B

/-- A local attractor in the uniform-neighborhood sense. No global
attraction or transitivity assumption is inserted. The uniform-neighborhood
attraction convention is an explicit supplement to the Rössler paper,
which does not give a full abstract definition of an attractor. -/
def Attractor (K : Set (PhaseSpace n)) : Prop :=
  D.CompactInvariantSet K ∧
    ∃ V : Set (PhaseSpace n), IsOpen V ∧ K ⊆ V ∧ V ⊆ D.U ∧
      ∀ B : Set (PhaseSpace n), B ⊆ V → Bornology.IsBounded B →
        D.UniformlyAttracts K B

/-- SUPPLEMENTARY CONVENTION from Wikipedia, "Lyapunov dimension":
"strange" means that the Hausdorff dimension is not an integer.
The 2018 Rössler paper itself does not define this qualifier.
This is not the assertion "there is a positive Lyapunov exponent", nor
is it a hidden transitivity requirement. -/
def StrangeAttractorNonintegerHausdorff (K : Set (PhaseSpace n)) : Prop :=
  D.Attractor K ∧
    ¬ ∃ m : ℕ, dimH K = (m : ENNReal)

/-- Orbital Lyapunov stability, relative to the phase domain, not attraction.
We use the negation of this property for "unstable"; we do not silently
replace instability by the stronger positive-Floquet-exponent test. -/
def OrbitallyStable (u0 : PhaseSpace n) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ D.U,
        (∃ v ∈ Orbit D.φ u0, dist u v < δ) →
        ∀ t : ℝ, 0 ≤ t →
          ∃ v ∈ Orbit D.φ u0, dist (D.φ t u) v < ε


def UnstablePeriodicOrbit (u0 : PhaseSpace n) : Prop :=
  PeriodicSolution D.φ u0 ∧ ¬ D.OrbitallyStable u0

/-- Singular values, indexed from zero in Lean. Index i denotes sigma_(i+1)
in the literature. They are sorted by decreasing magnitude, with multiplicity. -/
def σ (t : ℝ) (u : PhaseSpace n) (i : ℕ) : ℝ :=
  (fderiv ℝ (D.φ t) u).toLinearMap.singularValues i

/-- LE_(i+1)(t,u) = log(sigma_(i+1)(t,u)) / t, used only for t > 0. -/
def finiteTimeLE (t : ℝ) (u : PhaseSpace n) (i : ℕ) : ℝ :=
  Real.log (D.σ t u i) / t

/-- Upper singular-value Lyapunov exponents. On a compact invariant set of
this finite-dimensional injective C1 flow the relevant rates are bounded;
using a real-valued limsup there does not turn an infinite exponent into zero. -/
def upperLE (u : PhaseSpace n) (i : ℕ) : ℝ :=
  Filter.limsup (fun t : ℝ => D.finiteTimeLE t u i) atTop

end C1DynamicalSystem

/-- Sum of the first k exponents; zero-based Lean indexing. -/
def exponentSum (rates : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, rates i

/-- The largest index having nonnegative partial sum. The set is finite,
nonempty (it contains 0), and bounded above by n. -/
def kaplanYorkeIndex (n : ℕ) (rates : ℕ → ℝ) : ℕ :=
  sSup {j : ℕ | j ≤ n ∧ 0 ≤ exponentSum rates j}

/-- Kaplan--Yorke formula, including the endpoint convention d_KY = n.
When all exponents are negative, j = 0 and the value is 0. -/
def kaplanYorkeDimension (n : ℕ) (rates : ℕ → ℝ) : ℝ :=
  let j := kaplanYorkeIndex n rates
  if j = n then (n : ℝ)
  else (j : ℝ) + exponentSum rates j / |rates j|

/-! ## Singular-value functions and Lyapunov dimensions -/

/-- The singular-value function ω_d(A). For integer d this is the product
of the first d singular values, including the empty product ω_0(A) = 1.
For noninteger d, interpolate with σ_(⌊d⌋+1)^(d-⌊d⌋).
Only orders d ∈ [0,n] are used in the dimension definitions. -/
def singularValueFunction {n : ℕ} (A : PhaseSpace n →ₗ[ℝ] PhaseSpace n)
    (d : ℝ) : ℝ :=
  let k := ⌊d⌋₊
  let product := ∏ i ∈ Finset.range k, A.singularValues i
  if d = (k : ℝ) then product
  else product * Real.rpow (A.singularValues k) (d - (k : ℝ))

namespace C1DynamicalSystem

variable {n : ℕ} (D : C1DynamicalSystem n)

/-- ω_d(Dφᵗ(u)), with zero-based singular-value indexing. -/
def ω (d t : ℝ) (u : PhaseSpace n) : ℝ :=
  singularValueFunction (fderiv ℝ (D.φ t) u).toLinearMap d

/-- t⁻¹ log ω_d(Dφᵗ(u)). The extended-real logarithm assigns -∞ at zero.
Only positive times are relevant to the limits below. -/
def singularValueGrowth (d t : ℝ) (u : PhaseSpace n) : EReal :=
  ((t⁻¹ : ℝ) : EReal) *
    (if D.ω d t u = 0 then ⊥ else (Real.log (D.ω d t u) : EReal))

/-- Upper exponential growth rate of ω_d(Dφᵗ(u)), preserving infinite rates. -/
def upperSingularValueGrowth (d : ℝ) (u : PhaseSpace n) : EReal :=
  Filter.limsup (fun t : ℝ => D.singularValueGrowth d t u) atTop

/-- S_k(u) = limsup_(t→∞) ∑_(i=1)^k ν_i(t,u), with S_0 = 0.
The real-valued convention is intended for finite rates on compact invariant sets. -/
def cumulativeUpperLE (u : PhaseSpace n) (k : ℕ) : ℝ :=
  if k = 0 then 0
  else Filter.limsup (fun t : ℝ => exponentSum (D.finiteTimeLE t u) k) atTop

/-- Relative upper exponent ν̂_(i+1) = S_(i+1) - S_i (zero-based indexing). -/
def relativeUpperLE (u : PhaseSpace n) (i : ℕ) : ℝ :=
  D.cumulativeUpperLE u (i + 1) - D.cumulativeUpperLE u i

end C1DynamicalSystem

/-- Canonical local Lyapunov dimension:
inf {d ∈ [0,n] : limsup_(t→∞) t⁻¹ log ω_d(Dφᵗ(u)) < 0}.
The finite-dimensional endpoint convention assigns n when the contraction
set is empty. Inserting n implements the infimum in the bounded interval.
This is dimᴱ_L in the updated manuscript, Definition 9. -/
def localLyapunovDimension {n : ℕ}
    (D : C1DynamicalSystem n) (u : PhaseSpace n) : EReal :=
  sInf (insert (n : EReal) {a : EReal | ∃ d : ℝ,
    d ∈ Icc (0 : ℝ) (n : ℝ) ∧ a = (d : EReal) ∧ D.upperSingularValueGrowth d u < 0})

/-- D₅: Kaplan--Yorke formula applied to the separately taken upper
singular-value exponents ν̄_i(u) = limsup_(t→∞) ν_i(t,u). -/
def kaplanYorkeDimensionOfUpperLE {n : ℕ}
    (D : C1DynamicalSystem n) (u : PhaseSpace n) : ℝ :=
  kaplanYorkeDimension n (D.upperLE u)

/-- D₆: Kaplan--Yorke formula applied to the relative upper exponents
ν̂_j(u) = S_j(u) - S_(j-1)(u). -/
def kaplanYorkeDimensionOfRelativeUpperLE {n : ℕ}
    (D : C1DynamicalSystem n) (u : PhaseSpace n) : ℝ :=
  kaplanYorkeDimension n (D.relativeUpperLE u)

/-- Local dimension of the single map φᵗ, from Definition 9:
sup {d ∈ [0,n] : ω_d(Dφᵗ(u)) > 1}. Empty sets have value 0.
The strict inequality is the manuscript's convention. -/
def finiteTimeLyapunovDimensionAt {n : ℕ}
    (D : C1DynamicalSystem n) (t : ℝ) (u : PhaseSpace n) : ℝ :=
  sSup {d : ℝ | d ∈ Icc (0 : ℝ) (n : ℝ) ∧ 1 < D.ω d t u}

/-- Lyapunov dimension of the single map φᵗ on K. -/
def finiteTimeLyapunovDimension {n : ℕ}
    (D : C1DynamicalSystem n) (t : ℝ) (K : Set (PhaseSpace n)) : ℝ :=
  sSup (finiteTimeLyapunovDimensionAt D t '' K)

/-- Lyapunov dimension of the dynamical system on K:
inf_(t>0) dim_L(φᵗ,K), as in Definition 9 of the updated manuscript. -/
def lyapunovDimension {n : ℕ}
    (D : C1DynamicalSystem n) (K : Set (PhaseSpace n)) : ℝ :=
  sInf {a : ℝ | ∃ t : ℝ, 0 < t ∧ a = finiteTimeLyapunovDimension D t K}

/-- The manuscript's global exponential-growth dimension dimᴱ_L({φᵗ},K).
The spatial maximum is expressed as a supremum. A strictly negative limiting
rate must exist, matching the manuscript's limit rather than assuming it.
The empty infimum has value +∞. No equality with `lyapunovDimension` is
asserted here; Proposition 10 requires a separate proof and its hypotheses. -/
def globalLyapunovDimension {n : ℕ}
    (D : C1DynamicalSystem n) (K : Set (PhaseSpace n)) : EReal :=
  sInf {a : EReal | ∃ d : ℝ,
    d ∈ Icc (0 : ℝ) (n : ℝ) ∧ a = (d : EReal) ∧
      ∃ rate : EReal, rate < 0 ∧
        Tendsto (fun t : ℝ => sSup (D.singularValueGrowth d t '' K)) atTop (𝓝 rate)}

/-- Spatial supremum of the canonical local Lyapunov dimensions.
This is the target in the manuscript's global Eden conjecture. -/
def supremumLocalLyapunovDimension {n : ℕ}
    (D : C1DynamicalSystem n) (K : Set (PhaseSpace n)) : EReal :=
  sSup (localLyapunovDimension D '' K)

/-- Finite-dimensional critical-path condition, using the canonical local
dimension and the manuscript's set dimension. -/
def CriticalPath {n : ℕ} (D : C1DynamicalSystem n)
    (K : Set (PhaseSpace n)) (u : PhaseSpace n) : Prop :=
  u ∈ K ∧ (lyapunovDimension D K : EReal) ≤ localLyapunovDimension D u

end Eden
