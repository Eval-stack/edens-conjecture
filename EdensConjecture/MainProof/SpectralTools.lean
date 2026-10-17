import EdensConjecture.EStatementDefinitions

/-!
# Auxiliary spectral calculations

Finite-time Kaplan--Yorke values used in the spectral calculations.
The conjecture statements use `Eden.localLyapunovDimension` from
`EStatementDefinitions`.
-/

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology
namespace Eden

/-- Kaplan--Yorke value at a fixed time, used in spectral calculations. -/
def finiteTimeKaplanYorkeValue {n : ℕ}
    (D : C1DynamicalSystem n) (t : ℝ) (u : PhaseSpace n) : ℝ :=
  kaplanYorkeDimension n (D.finiteTimeLE t u)

/-- Spatial supremum of finite-time Kaplan--Yorke values. -/
def finiteTimeKaplanYorkeSupremum {n : ℕ}
    (D : C1DynamicalSystem n) (t : ℝ) (K : Set (PhaseSpace n)) : ℝ :=
  sSup (finiteTimeKaplanYorkeValue D t '' K)

end Eden
