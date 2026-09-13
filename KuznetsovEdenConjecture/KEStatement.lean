import KuznetsovEdenConjectureDefinitions

/-!
# Kuznetsov–Eden conjectures

## Sources

[R] N. V. Kuznetsov, G. A. Leonov, T. N. Mokaev, A. Prasad,
    and M. D. Shrimali, "Finite-time Lyapunov dimension and hidden
    attractor of the Rabinovich system", Nonlinear Dynamics 92 (2018),
    267–285. DOI: 10.1007/s11071-018-4054-z.
    https://link.springer.com/article/10.1007/s11071-018-4054-z

    Primary wording for the self-excited conjecture: §5.3, p. 278,
    paragraph following equation (26).
    Attractors and their classification: §3 and Definition 1.
    Dimension definitions: §5.1, equations (12), (13), and (15).
    Preprint: https://arxiv.org/abs/1504.04723

[W] Wikipedia, "Eden's conjecture", subsection
    "Kuznetsov–Eden's conjecture", revision 1372866622.
    https://en.wikipedia.org/w/index.php?title=Eden%27s_conjecture&oldid=1372866622

    Provisional wording source for the separate hidden-attractor conjecture.
    An equivalent standalone primary-source passage has not been verified.

[K] N. V. Kuznetsov, "The Lyapunov dimension and its estimation via
    the Leonov method", Physics Letters A 380 (2016), 2142–2149.
    https://arxiv.org/pdf/1602.05410v3

    Background on finite-dimensional smooth dynamical systems and dimension
    conventions. The strict comparison in this preprint's footnote 7 is
    distinct from the non-strict comparison in [R].

## Mathematical scope

The background framework represents C¹ evolution on an open subset of ℝⁿ,
with either continuous or discrete time. Continuous-time evolution is
required to arise from an autonomous C¹ differential equation. Discrete-time
maps are iterates of the time-one map. All singular values are obtained
from the actual derivatives of these maps.

The local-attractor convention is compactness, invariance, local attraction,
and inclusion-minimality, following the convention discussed in [R], §3.
The dimension formulas of [R] are written with ambient dimension n in place
of 3. Their use for maps follows the finite-dimensional framework of [K].

The background structure permits singular derivatives, whereas [K] imposes
nonsingularity in its standing assumptions. This difference in ambient scope
remains to be resolved for a complete source-to-formalization correspondence;
neither conjecture paragraph by itself specifies every background hypothesis.

## Formalization status

Four fixed declarations have admitted definition bodies:

* `TypicalSystem`: no precise typicality criterion has been identified
  in the cited conjecture passages.
* `unstableManifold`: the intended unstable manifold Wᵘ(u_eq) has not
  been constructed in this formalization.
* `Visualizes`: no exact mathematical visualization criterion has been
  identified in those passages.
* `localLyapunovDimension`: the infinite-time pointwise convention in
  the hidden-attractor sentence remains unresolved.

These are missing definitions, not proved mathematical facts. In particular,
`opaque` does not supply the missing semantics. They must be completed before
these declarations constitute fully specified mathematical conjectures.

The two negation theorems also have admitted proof bodies. They are unproved
targets, not refutations. There are six `sorry` bodies in total.

This file has not been compiler-checked.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace KuznetsovEden

/-! ## Conjectures -/

/--
Self-excited formulation: [R], §5.3, p. 278, after equation (26).

For a typical system, each self-excited attractor has Lyapunov dimension
bounded above by that of an unstable equilibrium whose unstable manifold
both meets its basin and visualizes it. The comparison is non-strict.
The equilibrium is not required to lie in the attractor.
-/
def KuznetsovEdenConjectureSelfExcited : Prop :=
  ∀ D : DynamicalSystem, TypicalSystem D →
    ∀ A : Set (PhaseSpace D.n), D.SelfExcitedAttractor A →
      ∃ u_eq : PhaseSpace D.n,
        D.UnstableEquilibrium u_eq ∧
        (unstableManifold D u_eq ∩ D.basinOfAttraction A).Nonempty ∧
        Visualizes D (unstableManifold D u_eq) A ∧
        D.lyapunovDimension A ≤ D.equilibriumLyapunovDimension u_eq

theorem KuznetsovEdenConjectureSelfExcited_False :
    ¬ KuznetsovEdenConjectureSelfExcited := by
  sorry

/--
Hidden-attractor formulation: attributed to [W].
An equivalent standalone primary-source passage has not been verified.

The maximum local Lyapunov dimension is attained on an unstable periodic
orbit contained in the hidden attractor. `IsGreatest` expresses both
attainment and domination of all other values on the attractor.

This follows the separate hidden-attractor sentence: it does not repeat
typicality, allow a stationary-point alternative, or impose global attraction
or a strange-attractor hypothesis. The local-dimension convention remains
an admitted definition, as recorded above.
-/
def KuznetsovEdenConjectureHidden : Prop :=
  ∀ D : DynamicalSystem,
    ∀ A : Set (PhaseSpace D.n), D.HiddenAttractor A →
      ∃ u₀ ∈ A,
        D.UnstablePeriodicOrbit u₀ ∧
        D.orbit u₀ ⊆ A ∧
        IsGreatest (localLyapunovDimension D '' A)
          (localLyapunovDimension D u₀)

theorem KuznetsovEdenConjectureHidden_False :
    ¬ KuznetsovEdenConjectureHidden := by
  sorry

end KuznetsovEden

end


