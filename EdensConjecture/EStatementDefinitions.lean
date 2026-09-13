import Mathlib

noncomputable section

open Set Filter TopologicalSpace
open scoped BigOperators Topology

namespace Eden

/-!
# Definitions

This file seeks to define terminology that is used to state Eden's Conjecture and its variants in `EStatement.lean`. Definitions used for the proof of Eden's Conjecture for `EMainProof.lean` are not necessarily here.
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

/-- Pointwise local Lyapunov dimension, with a fixed exponent-based convention:

  LE_i(u) = limsup_{t -> infinity} log(sigma_i(D phi^t(u))) / t,
  dim_L(u) = d_KY(LE_1(u), ..., LE_n(u)).

This is the pointwise Kaplan--Yorke construction in Kuznetsov--Alexeeva--Leonov,
arXiv:1410.2016v3, section 2 and Corollary 2; see also Kuznetsov,
arXiv:1602.05410v3, footnote 3. The limsup is taken separately for each
singular-value exponent BEFORE applying the Kaplan--Yorke formula.

This is not a limsup of finite-time dimensions, nor the thesis's fixed-index
formula. A spatial supremum of this function is not silently replaced by
`liminf (sup (finite-time local dimension))`, the set-dimension construction
in the Rössler note and Wikipedia's linked dimension article. -/
def localLyapunovDimension {n : ℕ}
    (D : C1DynamicalSystem n) (u : PhaseSpace n) : ℝ :=
  kaplanYorkeDimension n (D.upperLE u)

/-! ## The thesis's Hilbert-space and s-number framework -/

section Thesis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Compact + strict contraction. For a bounded linear map between Hilbert
spaces, compactness is equivalently relative compactness of the unit-ball image. -/
def CCOperator (A : H →L[ℝ] H) : Prop :=
  ∃ K C : H →L[ℝ] H,
    A = K + C ∧
    IsCompact (closure (K '' Metric.closedBall (0 : H) 1)) ∧ ‖C‖ < 1

/-- P is precisely the positive part (A* A)^(1/2): self-adjoint, positive,
and P*P = A*A. This relational characterization avoids choosing an arbitrary
operator under the name "positive part". -/
def PositivePart (A P : H →L[ℝ] H) : Prop :=
  (∀ x y : H, inner ℝ (P x) y = inner ℝ x (P y)) ∧
  (∀ x : H, 0 ≤ inner ℝ (P x) x) ∧
  (∀ x y : H, inner ℝ (P x) (P y) = inner ℝ (A x) (A y))

/-- Eden II.2.1, the inf--sup formula for s_j, with j >= 1. The explicit
FiniteDimensional condition prevents the default finrank of an infinite-
dimensional subspace from passing the dimension bound. -/
def sNumber (P : H →L[ℝ] H) (j : ℕ) : ℝ :=
  sInf {a : ℝ | ∃ F : Submodule ℝ H,
    FiniteDimensional ℝ F ∧ Module.finrank ℝ F ≤ j - 1 ∧
    a = sSup {b : ℝ | ∃ u : H,
      ‖u‖ = 1 ∧
      (∀ v : H, v ∈ F → inner ℝ u v = 0) ∧
      b = inner ℝ (P u) u}}

/-- Nonlinear semigroup and the hypotheses used in the thesis's local
Hausdorff-dimension estimate. The compact invariant set need not be asserted
to be a strange attractor or a global attractor. -/
structure ThesisSetting (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] where
  X : Set H
  nonempty_X : X.Nonempty
  compact_X : IsCompact X
  S : ℝ → H → H
  initial : ∀ u : H, S 0 u = u
  semigroup : ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
    ∀ u : H, S (t + s) u = S t (S s u)
  continuous_space : ∀ t : ℝ, 0 ≤ t → Continuous (S t)
  continuous_on_X :
    ContinuousOn (fun p : ℝ × H => S p.1 p.2) ((Ioi 0) ×ˢ X)
  invariant_X : ∀ t : ℝ, 0 ≤ t → S t '' X = X
  S' : ℝ → H → H →L[ℝ] H
  derivative_continuous :
    ContinuousOn (fun p : ℝ × H => S' p.1 p.2) ((Ioi 0) ×ˢ X)
  derivative_injective : ∀ t : ℝ, 0 < t → ∀ u ∈ X,
    Function.Injective (S' t u)
  derivative_CC : ∀ t : ℝ, 0 < t → ∀ u ∈ X, CCOperator (S' t u)
  derivative_cocycle : ∀ t s : ℝ, 0 < t → 0 < s → ∀ u ∈ X,
    S' (t + s) u = (S' t (S s u)).comp (S' s u)
  short_time_bound : ∃ M : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
    ∀ u ∈ X, ‖S' t u‖ ≤ M
  P : ℝ → H → H →L[ℝ] H
  positive_part : ∀ t : ℝ, 0 < t → ∀ u ∈ X,
    PositivePart (S' t u) (P t u)
  c : ℝ → ℝ
  remainder : ℝ → ℝ
  c_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ c t
  remainder_nonneg : ∀ r : ℝ, 0 ≤ r → 0 ≤ remainder r
  remainder_zero : remainder 0 = 0
  remainder_small :
    Tendsto (fun r : ℝ => remainder r / r) (𝓝[>] 0) (𝓝 0)
  frechet_type_condition : ∀ t : ℝ, 0 < t → ∀ u ∈ X, ∀ u0 ∈ X,
    ‖S t u - S t u0 - S' t u0 (u - u0)‖ ≤ c t * remainder ‖u - u0‖

namespace ThesisSetting

variable (D : ThesisSetting H)

/-- s_j(t,u), with the thesis's one-based indexing. -/
def s (j : ℕ) (t : ℝ) (u : H) : ℝ :=
  sNumber (D.P t u) j

/-- w_k(t,u) = s_1(t,u) ... s_k(t,u), thesis III.3.7. -/
def w (k : ℕ) (t : ℝ) (u : H) : ℝ :=
  ∏ i ∈ Finset.range k, D.s (i + 1) t u

/-- log 0 = -infinity, not Lean's real-log-at-zero convention. Only
nonnegative inputs occur in the defining spectral expressions. -/
def extendedLog (r : ℝ) : EReal :=
  if r = 0 then ⊥ else (Real.log r : EReal)

/-- The cumulative LOCAL exponents use LIMSUP, not a presumed limit.
This is thesis II.4.8 / III.3.14. -/
def cumulativeLocalExponent (k : ℕ) (u : H) : EReal :=
  Filter.limsup
    (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * extendedLog (D.w k t u)) atTop

/-- The precise regime in which the displayed local-exponent ratio below
uses real numbers. This is an explicit hypothesis, not conversion of
infinite exponents to real zero. The same mu is constrained by every
cumulative equality up to N+1. -/
def RealLocalSpectrumThrough (N : ℕ) (μ : ℕ → H → ℝ) : Prop :=
  ∀ u ∈ D.X, ∀ k : ℕ, k ≤ N + 1 →
    ((∑ i ∈ Finset.range k, μ (i + 1) u : ℝ) : EReal) =
      D.cumulativeLocalExponent k u

/-- N is the FIRST integer for which the (N+1)-term local sum is negative
at EVERY point of X. N is globally fixed, not reselected at each u. -/
def FirstDimensionIndex (N : ℕ) (μ : ℕ → H → ℝ) : Prop :=
  (∀ u ∈ D.X, (∑ i ∈ Finset.range (N + 1), μ (i + 1) u) < 0) ∧
  (∀ m : ℕ, m < N →
    ¬ (∀ u ∈ D.X, (∑ i ∈ Finset.range (m + 1), μ (i + 1) u) < 0))

/-- Thesis III.1.3. Deliberately no pointwise Kaplan--Yorke reindexing,
no clipping at 0 or N, and no maximum substituted for this ratio. -/
def localLyapunovDimension (_D : ThesisSetting H)
    (N : ℕ) (μ : ℕ → H → ℝ) (u0 : H) : ℝ :=
  (N : ℝ) + (∑ i ∈ Finset.range N, μ (i + 1) u0) / |μ (N + 1) u0|

/-- The fixed-N singular-value expression used in III.1.26--1.28. -/
def dimensionExpression (N : ℕ) (d t : ℝ) (u : H) : ℝ :=
  D.w N t u * Real.rpow (D.s (N + 1) t u) (d - (N : ℝ))

/-- d_DO = inf{d > 0 : sup_X w_N(t,u) s_(N+1)(t,u)^(d-N) -> 0}.
The codomain EReal makes infimum of the empty set +infinity, as the
thesis explicitly prescribes. Convergence to zero is NOT replaced by
exponential convergence (that is the distinct Remark III.1.38). -/
def douadyOesterleDimension (N : ℕ) : EReal :=
  sInf {a : EReal | ∃ d : ℝ,
    0 < d ∧ a = (d : EReal) ∧
    Tendsto
      (fun t : ℝ => sSup (D.dimensionExpression N d t '' D.X))
      atTop (𝓝 (0 : ℝ))}

/-- The dimension-bound use of "critical path" on printed p.97.
This is NOT asserted to be the thesis's only use of that terminology. -/
def CriticalPath (N : ℕ) (μ : ℕ → H → ℝ) (u0 : H) : Prop :=
  u0 ∈ D.X ∧
    D.douadyOesterleDimension N ≤ (D.localLyapunovDimension N μ u0 : EReal)


/-- Global attraction of X in the ambient Hilbert space.
Compactness, nonemptiness and invariance are already fields of the setting.
This additional property is used by the global supremum-attainment reading,
not by the compact-invariant-set reading of Question 1. -/
def IsGlobalAttractor : Prop :=
  ∀ B : Set H, Bornology.IsBounded B →
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → ∀ u ∈ B,
          ∃ v ∈ D.X, dist (D.S t u) v < ε

/-- The supremum of the thesis's local dimensions on X.
The use of EReal makes an unbounded-above image have supremum +infinity;
it does not turn an unbounded real supremum into Lean's default real value. -/
def supremumLocalLyapunovDimension (N : ℕ) (μ : ℕ → H → ℝ) : EReal :=
  sSup ((fun u : H => (D.localLyapunovDimension N μ u : EReal)) '' D.X)

/-- Supremum attainment by a stationary or periodic solution, using exactly
III.1.3 for the local dimension. This is a maximizing-path condition;
`CriticalPath` instead requires only the non-strict dimension bound. -/
def StationaryOrPeriodicSupremumAttainment
    (N : ℕ) (μ : ℕ → H → ℝ) : Prop :=
  ∃ u0 ∈ D.X,
    (StationarySolution D.S u0 ∨ PeriodicSolution D.S u0) ∧
    (D.localLyapunovDimension N μ u0 : EReal) =
      D.supremumLocalLyapunovDimension N μ

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
end Thesis


end Eden

