import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-! Scalar formulas for the direct Cantor-comb construction.
These preliminary identities do not assert regularity of the full piecewise flow. -/

noncomputable section
namespace Eden.StrangeProof.Direct

def contraction : ℝ := 3 / 7

theorem lower_dimension_ratio : (1 : ℝ) < 2 ^ 5 * contraction ^ 4 := by
  norm_num [contraction]

theorem upper_dimension_ratio : (2 : ℝ) ^ 6 * contraction ^ 5 < 1 := by
  norm_num [contraction]

/-- Restoring drift outside the unit interval. -/
def restoring (u : ℝ) : ℝ := max (u - 1) 0 ^ 2 - max (-u) 0 ^ 2

theorem restoring_of_neg {u : ℝ} (hu : u < 0) : restoring u = -u ^ 2 := by
  simp [restoring, max_eq_right (show u - 1 ≤ 0 by linarith),
    max_eq_left (show 0 ≤ -u by linarith)]

theorem restoring_of_mem {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    restoring u = 0 := by
  simp [restoring, max_eq_right (sub_nonpos.mpr hu.2),
    max_eq_right (neg_nonpos.mpr hu.1)]

theorem restoring_of_gt {u : ℝ} (hu : 1 < u) : restoring u = (u - 1) ^ 2 := by
  simp [restoring, max_eq_left (sub_nonneg.mpr hu.le),
    max_eq_right (show -u ≤ 0 by linarith)]

/-- Explicit flow of the restoring equation. -/
def scalarFlow (t u : ℝ) : ℝ :=
  if u < 0 then u / (1 - t * u)
  else if 1 < u then 1 + (u - 1) / (1 + t * (u - 1))
  else u

theorem scalarFlow_zero (u : ℝ) : scalarFlow 0 u = u := by
  unfold scalarFlow
  split_ifs <;> ring

theorem scalarFlow_fixed {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    scalarFlow t u = u := by
  simp [scalarFlow, not_lt.mpr hu.1, not_lt.mpr hu.2]

theorem lower_denominator_pos {t u : ℝ} (ht : 0 ≤ t) (hu : u < 0) :
    0 < 1 - t * u := by
  have := mul_nonpos_of_nonneg_of_nonpos ht hu.le
  linarith

theorem upper_denominator_pos {t u : ℝ} (ht : 0 ≤ t) (hu : 1 < u) :
    0 < 1 + t * (u - 1) := by
  have := mul_nonneg ht (sub_nonneg.mpr hu.le)
  linarith

/-- The negative-half-line branch for the second scalar equation. -/
def negativeFlow (a t v : ℝ) : ℝ :=
  -a * ((a - v) - (a + v) * Real.exp (-2 * a * t)) /
    ((a - v) + (a + v) * Real.exp (-2 * a * t))

theorem negativeFlow_zero {a : ℝ} (ha : 0 < a) (v : ℝ) :
    negativeFlow a 0 v = v := by
  simp only [negativeFlow, mul_zero, Real.exp_zero, mul_one]
  rw [show a - v + (a + v) = 2 * a by ring]
  field_simp
  <;> nlinarith

/-- All branches of the second scalar formula from Appendix A.
The intended parameter range is `0 ≤ a ≤ 1/16` and time is nonnegative. -/
def forcedScalarFlow (a t v : ℝ) : ℝ :=
  if a = 0 then scalarFlow t v
  else if v ≤ 0 then negativeFlow a t v
  else if v ≤ 1 then
    if t ≤ v / a ^ 2 then v - a ^ 2 * t
    else negativeFlow a (t - v / a ^ 2) 0
  else
    let τ := Real.arctan ((v - 1) / a) / a
    if t ≤ τ then 1 + a * Real.tan (Real.arctan ((v - 1) / a) - a * t)
    else if t ≤ τ + 1 / a ^ 2 then 1 - a ^ 2 * (t - τ)
    else negativeFlow a (t - τ - 1 / a ^ 2) 0

theorem negativeFlow_fixed {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    negativeFlow a t (-a) = -a := by
  simp only [negativeFlow, add_neg_cancel, zero_mul, sub_zero, add_zero]
  rw [sub_neg_eq_add]
  exact mul_div_cancel_right₀ (-a) (by simpa [two_mul] using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha)

theorem forcedScalarFlow_graph_fixed {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    forcedScalarFlow a t (-a) = -a := by
  by_cases hz : a = 0
  · subst a
    simp [forcedScalarFlow, scalarFlow]
  · simp only [forcedScalarFlow, if_neg hz, if_pos (neg_nonpos.mpr ha)]
    exact negativeFlow_fixed hz t

theorem forcedScalarFlow_tooth_fixed {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) : forcedScalarFlow 0 t v = v := by
  simpa [forcedScalarFlow] using scalarFlow_fixed hv t

theorem forcedScalarFlow_zero {a : ℝ} (ha : 0 ≤ a) (v : ℝ) :
    forcedScalarFlow a 0 v = v := by
  by_cases hz : a = 0
  · simp [forcedScalarFlow, hz, scalarFlow_zero]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  by_cases hv0 : v ≤ 0
  · simpa only [forcedScalarFlow, if_neg hz, if_pos hv0] using negativeFlow_zero hap v
  have hvp : 0 < v := lt_of_not_ge hv0
  by_cases hv1 : v ≤ 1
  · simp [forcedScalarFlow, hz, hv0, hv1, div_nonneg hvp.le (sq_nonneg a)]
  have hτ : 0 ≤ Real.arctan ((v - 1) / a) / a := by
    apply div_nonneg _ ha
    apply Real.arctan_nonneg.mpr
    exact div_nonneg (by linarith) ha
  simp only [forcedScalarFlow, if_neg hz, if_neg hv0, if_neg hv1, if_pos hτ,
    mul_zero, sub_zero, Real.tan_arctan]
  field_simp
  <;> ring

end Eden.StrangeProof.Direct
