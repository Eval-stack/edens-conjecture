import Mathlib

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace KuznetsovEden

/--
# Definitions

This file seeks to define terminology that is used to state the two conjectures listed as the Kuznetsov-Eden Conjecture in `KuznetsovEdenConjecture.lean`. Definitions used for the proof of the Kuznetsov-Eden Conjecture for `EdensConjectureProof.lean` are not necessarily here.
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

/-! ## Source vocabulary and incomplete definitions -/

/--
The typical-system qualification in [R].

Admitted definition: the cited conjecture passage does not fix a space of
systems together with a topology, measure, or another typicality criterion.
-/
opaque TypicalSystem : DynamicalSystem → Prop := by
  sorry

/--
The unstable manifold Wᵘ(u_eq) appearing in [R].

Admitted definition: the manifold's mathematical construction and its
relation to the evolution have not been implemented here.
-/
opaque unstableManifold (D : DynamicalSystem) :
    PhaseSpace D.n → Set (PhaseSpace D.n) := by
  sorry

/--
The condition that the unstable manifold W visualizes the attractor A.

Admitted definition: the cited passages do not specify an exact mathematical
criterion for this observational qualification. Basin intersection alone is
not substituted for it.
-/
opaque Visualizes (D : DynamicalSystem) :
    Set (PhaseSpace D.n) → Set (PhaseSpace D.n) → Prop := by
  sorry

/--
The pointwise local Lyapunov dimension in [W]'s hidden-attractor sentence.

Admitted definition: the sentence does not uniquely select an infinite-time
pointwise convention. In particular, a time limit of finite-time dimensions
is not identified with the Kaplan–Yorke function of upper Lyapunov exponents.
-/
opaque localLyapunovDimension (D : DynamicalSystem) :
    PhaseSpace D.n → ℝ := by
  sorry

end KuznetsovEden

end
