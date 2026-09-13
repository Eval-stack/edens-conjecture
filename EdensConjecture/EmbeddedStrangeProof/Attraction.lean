import EdensConjecture.EmbeddedStrangeProof.ScalarFlow
import EdensConjecture.EmbeddedStrangeProof.Gap

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

theorem gapFunction_scalarFlow {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    gapFunction (scalarFlow t x) = gapFunction x := by
  by_cases hx0 : x < 0
  · rw [gapFunction_zero_outside (fun h => (scalarFlow_neg ht hx0).not_ge h.1),
      gapFunction_zero_outside (fun h => hx0.not_ge h.1)]
  by_cases hx1 : 1 < x
  · rw [gapFunction_zero_outside (fun h => (scalarFlow_gt_one ht hx1).not_ge h.2),
      gapFunction_zero_outside (fun h => hx1.not_ge h.2)]
  · rw [scalarFlow_fixed ⟨le_of_not_gt hx0, le_of_not_gt hx1⟩]

theorem gapFunction_lower_of_far {x δ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hδ : 0 ≤ δ)
    (hfar : ∀ c ∈ cantorSet, δ ≤ |x - c|) : δ ^ 4 ≤ gapFunction x := by
  obtain ⟨hl0, hlx, hxu, hu1⟩ := endpoint_bounds hx
  have hl := hfar _ (lowerEndpoint_mem hx).1
  have hu := hfar _ (upperEndpoint_mem hx).1
  rw [abs_of_nonneg (sub_nonneg.mpr hlx)] at hl
  rw [abs_of_nonpos (sub_nonpos.mpr hxu)] at hu
  have hp : δ ^ 2 ≤ (x - lowerEndpoint x) ^ 2 := pow_le_pow_left₀ hδ hl 2
  have hq : δ ^ 2 ≤ (upperEndpoint x - x) ^ 2 := by
    apply pow_le_pow_left₀ hδ
    linarith
  have hm := mul_le_mul hp hq (sq_nonneg δ) (sq_nonneg (x - lowerEndpoint x))
  rw [gapFunction, if_pos hx]
  nlinarith [hm]

theorem exists_cantor_near_of_gap_small {x δ : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hδ : 0 ≤ δ) (hg : gapFunction x < δ ^ 4) : ∃ c ∈ cantorSet, |x - c| < δ := by
  by_contra! hfar
  exact hg.not_ge (gapFunction_lower_of_far hx hδ hfar)

theorem negativeFlow_denominator_pos {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : v ≤ 0) :
    0 < (a - v) + (a + v) * Real.exp (-2 * a * t) := by
  have he0 := Real.exp_pos (-2 * a * t)
  have he1 : Real.exp (-2 * a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h1 := mul_nonneg (neg_nonneg.mpr hv) (sub_nonneg.mpr he1)
  have h2 := mul_pos ha (show 0 < 1 + Real.exp (-2 * a * t) by linarith)
  nlinarith

theorem negativeFlow_nonpos {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : v ≤ 0) :
    negativeFlow a t v ≤ 0 := by
  have he0 := Real.exp_pos (-2 * a * t)
  have he1 : Real.exp (-2 * a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  apply div_nonpos_of_nonpos_of_nonneg _ (negativeFlow_denominator_pos ha ht hv).le
  apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
  have h1 := mul_nonneg ha.le (sub_nonneg.mpr he1)
  have h2 := mul_nonneg (neg_nonneg.mpr hv) (show 0 ≤ 1 + Real.exp (-2 * a * t) by linarith)
  nlinarith

theorem negativeFlow_add_parameter {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : v ≤ 0) :
    negativeFlow a t v + a =
      2 * a * (a + v) * Real.exp (-2 * a * t) /
        ((a - v) + (a + v) * Real.exp (-2 * a * t)) := by
  unfold negativeFlow
  rw [div_add' _ _ _ (negativeFlow_denominator_pos ha ht hv).ne']
  congr 1
  ring

theorem negativeFlow_ge_min {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : v ≤ 0) :
    min v (-a) ≤ negativeFlow a t v := by
  have hD := negativeFlow_denominator_pos ha ht hv
  have he0 := Real.exp_pos (-2 * a * t)
  have he1 : Real.exp (-2 * a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  by_cases hva : v ≤ -a
  · rw [min_eq_left hva]
    apply (le_div_iff₀ hD).mpr
    have hsq : a ^ 2 ≤ v ^ 2 := by nlinarith
    have hp := mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr he1)
    nlinarith
  · rw [min_eq_right (le_of_not_ge hva)]
    have hpos : 0 ≤ negativeFlow a t v + a := by
      rw [negativeFlow_add_parameter ha ht hv]
      apply div_nonneg _ hD.le
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha.le) (by linarith)) he0.le
    linarith

theorem negativeFlow_error_bound {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : v ≤ 0) :
    |negativeFlow a t v + a| ≤ 2 * |a + v| * Real.exp (-2 * a * t) := by
  have hD := negativeFlow_denominator_pos ha ht hv
  have he0 := Real.exp_pos (-2 * a * t)
  have he1 : Real.exp (-2 * a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hDa : a ≤ (a - v) + (a + v) * Real.exp (-2 * a * t) := by
    have h1 := mul_nonneg (neg_nonneg.mpr hv) (sub_nonneg.mpr he1)
    have h2 := mul_nonneg ha.le he0.le
    nlinarith
  rw [negativeFlow_add_parameter ha ht hv, abs_div, abs_of_pos hD,
    abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos ha, abs_of_pos he0]
  apply (div_le_iff₀ hD).mpr
  have hmul := mul_le_mul_of_nonneg_left hDa
    (show 0 ≤ 2 * |a + v| * Real.exp (-2 * a * t) by positivity)
  nlinarith

theorem negativeFlow_ge_parameter_sub_inv {a t v : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hv : v ≤ 0) : -a - 1 / t ≤ negativeFlow a t v := by
  have hD := negativeFlow_denominator_pos ha ht.le hv
  have he0 := Real.exp_pos (-2 * a * t)
  have he : (1 + 2 * a * t) * Real.exp (-2 * a * t) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * a * t)) he0.le
    rw [← Real.exp_add] at h
    have hz : 2 * a * t + -2 * a * t = 0 := by ring
    rw [hz, Real.exp_zero] at h
    nlinarith
  by_cases hva : 0 ≤ a + v
  · have hh : 0 ≤ negativeFlow a t v + a := by
      rw [negativeFlow_add_parameter ha ht.le hv]
      positivity
    have hi : 0 ≤ 1 / t := by positivity
    linarith
  · have hmul := mul_le_mul_of_nonpos_left he (le_of_not_ge hva)
    have hmain : 0 ≤ ((a - v) + (a + v) * Real.exp (-2 * a * t)) +
        t * (2 * a * (a + v) * Real.exp (-2 * a * t)) := by nlinarith
    have hfrac : -1 / t ≤ negativeFlow a t v + a := by
      rw [negativeFlow_add_parameter ha ht.le hv, div_le_div_iff₀ ht hD]
      nlinarith
    rw [neg_div] at hfrac
    linarith

end Eden.StrangeProof.Direct
