import KuznetsovEdenConjecture.KEStatementDefinitions

/-!
# Kuznetsov--Eden conjectures

## Sources

[K] Kuznetsov (2016), footnote 7, printed p.12:
https://arxiv.org/pdf/1602.05410v3

[R] Kuznetsov et al. (2018), paragraph following equation (26):
https://arxiv.org/pdf/1504.04723

[W] https://en.wikipedia.org/w/index.php?title=Eden%27s_conjecture&oldid=1372866622

## Formulation

The self-excited statement uses a non-strict dimension bound and requires
an unstable equilibrium whose unstable set intersects the attractor's basin.
It omits the additional visualization condition appearing in K and R.
Consequently, its equilibrium conclusion is weaker than those source
formulations. K uses a strict comparison; R uses a non-strict comparison.

Typicality means validity on a dense G-delta class in C1(R^n,R^n), equipped
with the compact-open C1 topology. The class may depend on dimension and
time kind. This is an explicit Baire-generic interpretation; the conjecture
passages do not specify a topology or a residual-class definition.

The hidden statement requires a periodic candidate whose local finite-time
dimension equals the attractor's set dimension. Local dimension takes the
time liminf at a point; set dimension takes the spatial supremum before the
time liminf. Both conjectures use this convention and are closed propositions.

The negation theorems are unfinished proof targets containing sorry.
-/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace KuznetsovEden

/-- Non-strict equilibrium dimension bound with an unstable-set basin connection. -/
def SelfExcitedDimensionBound (D : DynamicalSystem) : Prop :=
  ∀ A : Set (PhaseSpace D.n), D.SelfExcitedAttractor A →
    ∃ u_eq : PhaseSpace D.n,
      D.UnstableEquilibrium u_eq ∧
      (unstableManifold D u_eq ∩ D.basinOfAttraction A).Nonempty ∧
      D.lyapunovDimension A ≤ D.equilibriumLyapunovDimension u_eq

/-- Baire-generic equilibrium bound in every positive dimension and time kind. -/
def KuznetsovEdenConjectureSelfExcited : Prop :=
  ∀ n : ℕ, 0 < n → ∀ kind : TimeKind,
    ∃ T : Set (C1Equation n), TypicalClass T ∧
      ∀ F : C1Equation n, TypicalSystem T F →
        ∀ D : DynamicalSystem, RealizesEquation F kind D →
          SelfExcitedDimensionBound D

/-- Negation of the conjecture; proof incomplete. -/
theorem KuznetsovEdenConjectureSelfExcited_False :
    ¬ KuznetsovEdenConjectureSelfExcited := by
  sorry

/-- The finite-time set dimension is attained on an unstable periodic orbit
embedded in each hidden attractor. -/
def KuznetsovEdenConjectureHidden : Prop :=
  ∀ D : DynamicalSystem,
    ∀ A : Set (PhaseSpace D.n), D.HiddenAttractor A →
      ∃ u₀ ∈ A,
        D.UnstablePeriodicOrbit u₀ ∧
        D.orbit u₀ ⊆ A ∧
        localLyapunovDimension D u₀ = D.lyapunovDimension A

/-- Negation of the conjecture; proof incomplete. -/
theorem KuznetsovEdenConjectureHidden_False :
    ¬ KuznetsovEdenConjectureHidden := by
  sorry

end KuznetsovEden
end
