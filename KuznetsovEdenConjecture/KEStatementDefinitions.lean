import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Baire.Lemmas

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace KuznetsovEden

/-!
# Kuznetsov--Eden: explicit conventions

Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

[R] Kuznetsov et al., Finite-time Lyapunov dimension and hidden attractor
of the Rabinovich system, Nonlinear Dynamics 92 (2018), 267--285.
https://arxiv.org/pdf/1504.04723
Attractors: section 3 and Definition 1. Dimensions: equations (12), (13),
(15). Later non-strict self-excited assertion: paragraph following equation (26).

[L] Kuznetsov--Alexeeva--Leonov, Invariance of Lyapunov exponents and
Lyapunov dimension for regular and irregular linearizations, section 2.
https://arxiv.org/html/1410.2016v3

[K] Kuznetsov, The Lyapunov dimension and its estimation via the Leonov
method. https://arxiv.org/pdf/1602.05410v3
The self-excited wording is based on footnote 7 (printed p.12), with the
user-requested non-strict comparison in place of the original strict one.
The nonsingular-derivative standing assumption is imposed below.

[W] https://en.wikipedia.org/w/index.php?title=Eden%27s_conjecture&oldid=1372866622
W supplies the separate hidden sentence; an equivalent standalone primary
source passage has not been verified.

Explicit supplementary choices, not uniquely prescribed by R/W:
* Typicality means residual validity in a SPECIFIED topological system space.
  The statement is parameterized by this space, rather than silently choosing
  a topology on the proof-containing DynamicalSystem structure.
* Visualization means an orbit from the indicated set has omega-limit A.
* The unstable set is defined through complete backward histories converging
  to the equilibrium. At a hyperbolic equilibrium this has the customary
  unstable-manifold interpretation. No hyperbolicity hypothesis is inserted.
* Pointwise dimension is the Kaplan--Yorke function of upper singular-value
  exponents (L), not a time limit of finite-time dimensions. These constructions
  are not identified. The real-valued exponent convention is used on compact
  invariant sets of the nonsingular finite-dimensional systems below, where
  the exponential growth rates are bounded. No claim about escaping orbits
  with infinite exponents is made.
-/

/-! ## Dynamical systems -/

/-- Euclidean phase space ℝⁿ. -/
abbrev PhaseSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Continuous time or discrete time, both represented inside ℝ. -/
inductive TimeKind where
  | continuous
  | discrete

/-- The admissible times: ℝ≥0 for a flow, ℕ for an iterated map. -/
def TimeKind.admissible (kind : TimeKind) (t : ℝ) : Prop :=
  match kind with
  | .continuous => 0 ≤ t
  | .discrete => ∃ k : ℕ, t = (k : ℝ)

/--
A C¹ evolution {φᵗ} on an open phase domain U ⊆ ℝⁿ.

The semigroup identities are required only at admissible times. In the
continuous-time case, `generated_by_ODE` identifies an autonomous C¹ vector
field whose forward solutions are the trajectories. In the discrete-time
case, the semigroup identities identify φᵏ with the k-th iterate of φ¹.
-/
structure DynamicalSystem where
  n : ℕ
  n_pos : 0 < n
  kind : TimeKind
  U : Set (PhaseSpace n)
  U_open : IsOpen U
  U_nonempty : U.Nonempty
  φ : ℝ → PhaseSpace n → PhaseSpace n
  identity : ∀ u ∈ U, φ 0 u = u
  forward_invariant : ∀ t, kind.admissible t → MapsTo (φ t) U U
  semigroup : ∀ t s, kind.admissible t → kind.admissible s →
    ∀ u ∈ U, φ (t + s) u = φ t (φ s u)
  C1 : ∀ t, kind.admissible t → ContDiffOn ℝ 1 (φ t) U
  continuous_time : kind = .continuous →
    ContinuousOn (fun p : ℝ × PhaseSpace n => φ p.1 p.2) ((Ici 0) ×ˢ U)
  derivative_injective : ∀ t, kind.admissible t → 0 < t →
    ∀ u ∈ U, Function.Injective (fderiv ℝ (φ t) u)
  generated_by_ODE : kind = .continuous →
    ∃ f : PhaseSpace n → PhaseSpace n,
      ContDiffOn ℝ 1 f U ∧
        ∀ u ∈ U, ∀ t : ℝ, 0 ≤ t →
          HasDerivWithinAt (fun s : ℝ => φ s u)
            (f (φ t u)) (Ici 0) t

namespace DynamicalSystem

variable (D : DynamicalSystem)

/-- The filter t → +∞ through the admissible times of the system. -/
def timeFilter : Filter ℝ :=
  (atTop : Filter ℝ) ⊓ Filter.principal {t | D.kind.admissible t}

/-- The forward orbit, including its initial point. -/
def orbit (u₀ : PhaseSpace D.n) : Set (PhaseSpace D.n) :=
  {u | ∃ t : ℝ, D.kind.admissible t ∧ D.φ t u₀ = u}

/-- An equilibrium; for discrete time, a fixed point. -/
def Equilibrium (u_eq : PhaseSpace D.n) : Prop :=
  u_eq ∈ D.U ∧
    ∀ t : ℝ, D.kind.admissible t → D.φ t u_eq = u_eq

/-- A nonstationary periodic trajectory, represented by an initial point. -/
def PeriodicTrajectory (u₀ : PhaseSpace D.n) : Prop :=
  u₀ ∈ D.U ∧ ¬ D.Equilibrium u₀ ∧
    ∃ T : ℝ, D.kind.admissible T ∧ 0 < T ∧ D.φ T u₀ = u₀

/--
Lyapunov stability of a set, relative to the phase domain U.
Instability is its negation, rather than a sufficient eigenvalue criterion.
-/
def LyapunovStable (K : Set (PhaseSpace D.n)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ D.U,
        (∃ v ∈ K, dist u v < δ) →
        ∀ t : ℝ, D.kind.admissible t →
          ∃ v ∈ K, dist (D.φ t u) v < ε

/-- An equilibrium that is not Lyapunov stable. -/
def UnstableEquilibrium (u_eq : PhaseSpace D.n) : Prop :=
  D.Equilibrium u_eq ∧ ¬ D.LyapunovStable {u_eq}

/-- A nonstationary periodic orbit that is not Lyapunov stable as a set. -/
def UnstablePeriodicOrbit (u₀ : PhaseSpace D.n) : Prop :=
  D.PeriodicTrajectory u₀ ∧ ¬ D.LyapunovStable (D.orbit u₀)

/-! ## Attractors and basins -/

/--
The basin of attraction of A: the distance from φᵗ(u₀) to A tends to zero.
The ε-formulation avoids a special convention for distance to the empty set.
-/
def basinOfAttraction (A : Set (PhaseSpace D.n)) : Set (PhaseSpace D.n) :=
  {u₀ | u₀ ∈ D.U ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, D.kind.admissible t → T ≤ t →
          ∃ v ∈ A, dist (D.φ t u₀) v < ε}

/-- A nonempty compact invariant subset of the phase domain. -/
def CompactInvariantSet (A : Set (PhaseSpace D.n)) : Prop :=
  A.Nonempty ∧ IsCompact A ∧ A ⊆ D.U ∧
    ∀ t : ℝ, D.kind.admissible t → D.φ t '' A = A

/-- Pointwise attraction from some ε-neighborhood of A, as in [R], §3. -/
def LocallyAttractive (A : Set (PhaseSpace D.n)) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∀ u ∈ D.U,
      (∃ v ∈ A, dist u v < ε) → u ∈ D.basinOfAttraction A

def LocallyAttractiveInvariantSet (A : Set (PhaseSpace D.n)) : Prop :=
  D.CompactInvariantSet A ∧ D.LocallyAttractive A

/--
An inclusion-minimal compact invariant locally attractive set.
This adopts the minimal-attractor convention discussed in [R], §3.
-/
def LocalAttractor (A : Set (PhaseSpace D.n)) : Prop :=
  D.LocallyAttractiveInvariantSet A ∧
    ∀ B : Set (PhaseSpace D.n), B ⊆ A →
      D.LocallyAttractiveInvariantSet B → A ⊆ B

/--
[R], Definition 1: the basin meets every neighborhood of some equilibrium.
The separate instability requirement belongs to the conjecture's conclusion.
-/
def SelfExcitedAttractor (A : Set (PhaseSpace D.n)) : Prop :=
  D.LocalAttractor A ∧
    ∃ u_eq : PhaseSpace D.n, D.Equilibrium u_eq ∧
      ∀ ε : ℝ, 0 < ε →
        (Metric.ball u_eq ε ∩ D.basinOfAttraction A).Nonempty

/-- [R], Definition 1: an attractor that is not self-excited. -/
def HiddenAttractor (A : Set (PhaseSpace D.n)) : Prop :=
  D.LocalAttractor A ∧ ¬ D.SelfExcitedAttractor A

/-! ## Singular values and Lyapunov dimensions -/

/--
σᵢ₊₁(t,u), the (i+1)-st singular value of Dφᵗ(u), in decreasing order.
`LinearMap.singularValues` uses zero-based indexing.
-/
def σ (t : ℝ) (u : PhaseSpace D.n) (i : ℕ) : ℝ :=
  (fderiv ℝ (D.φ t) u).toLinearMap.singularValues i

/--
The singular-value function ω_d(Dφᵗ(u)), used for 0 ≤ d ≤ n.
At d = j+s with 0 ≤ s < 1, its value is
σ₁ ⋯ σⱼ σⱼ₊₁^s. The cases d = 0 and d = n are handled separately.
-/
def ω (t : ℝ) (u : PhaseSpace D.n) (d : ℝ) : ℝ := by
  classical
  exact
    if d = 0 then 1
    else if d = (D.n : ℝ) then ∏ i ∈ Finset.range D.n, D.σ t u i
    else
      let j : ℕ := Nat.floor d
      (∏ i ∈ Finset.range j, D.σ t u i) *
        Real.rpow (D.σ t u j) (d - (j : ℝ))

/--
[R], equation (12), in ambient dimension n:
  dim_L(t,u) = max {d ∈ [0,n] : ω_d(Dφᵗ(u)) ≥ 1}.

The value is represented by the real supremum of the indicated nonempty
bounded set. For singular values, this supremum is a maximum. The set
contains 0 because ω₀ = 1, including when all singular values are below 1.
-/
def finiteTimeLocalLyapunovDimension (t : ℝ) (u : PhaseSpace D.n) : ℝ :=
  sSup {d : ℝ | 0 ≤ d ∧ d ≤ (D.n : ℝ) ∧ 1 ≤ D.ω t u d}

/-- [R], equation (13): dim_L(t,K) = sup_{u ∈ K} dim_L(t,u). -/
def finiteTimeLyapunovDimension (t : ℝ) (K : Set (PhaseSpace D.n)) : ℝ :=
  sSup (D.finiteTimeLocalLyapunovDimension t '' K)

/--
[R], equation (15):
  dim_L K = liminf_{t → +∞} sup_{u ∈ K} dim_L(t,u).
The spatial supremum is taken before the time limit.
-/
def lyapunovDimension (K : Set (PhaseSpace D.n)) : ℝ :=
  Filter.liminf (fun t : ℝ => D.finiteTimeLyapunovDimension t K) D.timeFilter

/-- The Lyapunov dimension of an equilibrium's singleton invariant set. -/
def equilibriumLyapunovDimension (u_eq : PhaseSpace D.n) : ℝ :=
  D.lyapunovDimension {u_eq}

end DynamicalSystem


/-! ## Backward histories and visualization -/

/-- Allowed times for a two-sided history: real times or integer times. -/
def TimeKind.signedAdmissible (kind : TimeKind) (t : ℝ) : Prop :=
  match kind with
  | .continuous => True
  | .discrete => ∃ k : ℤ, t = (k : ℝ)

/-- A complete past ending at x, consistent with the given forward evolution.
For a noninvertible map, existence of a history is required, not a selected
inverse branch. Values at other times play no role. -/
def BackwardHistory (D : DynamicalSystem) (x : PhaseSpace D.n)
    (γ : ℝ → PhaseSpace D.n) : Prop :=
  γ 0 = x ∧
  (∀ t, D.kind.signedAdmissible t → t ≤ 0 → γ t ∈ D.U) ∧
  (∀ t s, D.kind.signedAdmissible t → D.kind.admissible s →
    t + s ≤ 0 → D.φ s (γ t) = γ (t + s)) ∧
  (D.kind = .continuous → ContinuousOn γ (Iic 0))

/-- Global unstable set; identified with W^u for hyperbolic equilibria.
This definition does not postulate the unstable-manifold theorem. -/
def unstableManifold (D : DynamicalSystem) (p : PhaseSpace D.n) :
    Set (PhaseSpace D.n) :=
  {x | D.Equilibrium p ∧ ∃ γ : ℝ → PhaseSpace D.n,
    BackwardHistory D x γ ∧
    Tendsto γ ((atBot : Filter ℝ) ⊓
      Filter.principal {t | D.kind.signedAdmissible t}) (𝓝 p)}

/-- Omega-limit set in the ambient Euclidean space, through allowed times. -/
def omegaLimitSet (D : DynamicalSystem) (x : PhaseSpace D.n) :
    Set (PhaseSpace D.n) :=
  {y | ∀ ε : ℝ, 0 < ε → ∀ T : ℝ,
    ∃ t : ℝ, D.kind.admissible t ∧ T ≤ t ∧ dist (D.φ t x) y < ε}

/-- Explicit mathematical interpretation of "visualizes": a trajectory
from W approaches A and visits every part of A arbitrarily late.
The source does not uniquely specify this observational term. -/
def Visualizes (D : DynamicalSystem)
    (W A : Set (PhaseSpace D.n)) : Prop :=
  ∃ x ∈ W ∩ D.basinOfAttraction A, omegaLimitSet D x = A

/-- Pointwise finite-time dimension, using the same time filter as the set
construction. The set supremum is not moved outside this time limit. -/
def localLyapunovDimension (D : DynamicalSystem)
    (x : PhaseSpace D.n) : ℝ :=
  Filter.liminf (fun t => D.finiteTimeLocalLyapunovDimension t x) D.timeFilter

/-! ## Typicality relative to an explicit system space -/

/-- A residual class in the caller-specified topological space.
Use the intended C1 topology (or explicitly declare a parameter-family
interpretation). No topology or residual class is inferred from this name. -/
def TypicalClass {X : Type*} [TopologicalSpace X] (T : Set X) : Prop :=
  T ∈ residual X

end KuznetsovEden
end
