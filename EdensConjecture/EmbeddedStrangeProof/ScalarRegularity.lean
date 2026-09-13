import EdensConjecture.EmbeddedStrangeProof.Gap
import EdensConjecture.EmbeddedStrangeProof.ScalarFlow

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

def positiveRational (t x : ℝ) : ℝ := max x 0 ^ 2 / (1 + t * max x 0)
def positiveRationalDerivative (t x : ℝ) : ℝ :=
  (2 * max x 0 + t * max x 0 ^ 2) / (1 + t * max x 0) ^ 2

theorem positiveRational_denominator_pos {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    0 < 1 + t * max x 0 := by nlinarith [mul_nonneg ht (le_max_right x 0)]

theorem hasDerivAt_positiveRational {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivAt (positiveRational t) (positiveRationalDerivative t x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : positiveRational t =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [positiveRational, max_eq_right (le_of_lt (show y < 0 from hy))]
    simpa [positiveRationalDerivative, max_eq_right hx.le] using
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  · have hb : positiveRational t =O[𝓝 0] (fun y : ℝ => ‖y - 0‖ ^ 2) := by
      apply Asymptotics.IsBigO.of_bound'
      apply Eventually.of_forall
      intro y
      have hD := positiveRational_denominator_pos ht y
      have hn : 0 ≤ positiveRational t y := div_nonneg (sq_nonneg _) hD.le
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      simp only [sub_zero, norm_pow, Real.norm_eq_abs, sq_abs]
      by_cases hy : y ≤ 0
      · simpa [positiveRational, max_eq_right hy] using sq_nonneg y
      · have hyp : 0 ≤ y := le_of_not_ge hy
        simp only [positiveRational, max_eq_left hyp] at hD ⊢
        apply (div_le_iff₀ hD).mpr
        nlinarith [mul_nonneg (sq_nonneg y) (mul_nonneg ht hyp)]
    have hs := hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub (0 : ℝ) (by decide : 1 < 2))
    have hzero : positiveRational t 0 = 0 := by simp [positiveRational]
    have hd0 : positiveRationalDerivative t 0 = 0 := by simp [positiveRationalDerivative]
    rw [hasDerivAt_iff_isLittleO]
    simpa only [hzero, hd0, sub_zero, smul_zero] using hs
  · have heq : positiveRational t =ᶠ[𝓝 x] (fun y => y ^ 2 / (1 + t * y)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp only [positiveRational, max_eq_left (le_of_lt (show 0 < y from hy))]
    have hD : 1 + t * x ≠ 0 := by nlinarith [mul_nonneg ht hx.le]
    have hg := ((hasDerivAt_id x).pow 2).div
      ((hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).const_mul t)) hD
    have hf := hg.congr_of_eventuallyEq heq
    convert! hf using 1 <;> simp only [positiveRationalDerivative, max_eq_left hx.le, id_eq,
      Pi.add_apply, Pi.pow_apply]
    congr 1
    ring

theorem contDiff_positiveRational {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ 1 (positiveRational t) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_positiveRational ht x).differentiableAt, ?_⟩
  have heq : deriv (positiveRational t) = positiveRationalDerivative t :=
    funext fun x => (hasDerivAt_positiveRational ht x).deriv
  rw [heq]
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact pow_ne_zero 2 (positiveRational_denominator_pos ht x).ne'

theorem scalarFlow_eq_positiveRational {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    scalarFlow t x = x + t * positiveRational t (-x) - t * positiveRational t (x - 1) := by
  by_cases hx0 : x < 0
  · have hD := (lower_denominator_pos ht hx0).ne'
    simp only [scalarFlow, if_pos hx0, positiveRational,
      max_eq_left (show 0 ≤ -x by linarith), max_eq_right (show x - 1 ≤ 0 by linarith),
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_div, sub_zero]
    have hD' : 1 + t * -x = 1 - t * x := by ring
    rw [hD']
    apply (div_eq_iff hD).mpr
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hD]
    ring
  by_cases hx1 : 1 < x
  · have hD := (upper_denominator_pos ht hx1).ne'
    simp only [scalarFlow, if_neg hx0, if_pos hx1, positiveRational,
      max_eq_right (show -x ≤ 0 by linarith), max_eq_left (sub_nonneg.mpr hx1.le),
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_div, sub_zero]
    rw [add_div' _ _ _ hD]
    apply (div_eq_iff hD).mpr
    rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hD]
    ring
  · simp [scalarFlow, hx0, hx1, positiveRational, max_eq_right (show -x ≤ 0 by linarith),
      max_eq_right (show x - 1 ≤ 0 by linarith)]

theorem contDiff_scalarFlow {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ 1 (scalarFlow t) := by
  have heq : scalarFlow t = fun x => x + t * positiveRational t (-x) - t * positiveRational t (x - 1) :=
    funext (scalarFlow_eq_positiveRational ht)
  rw [heq]
  exact (contDiff_id.add (contDiff_const.mul ((contDiff_positiveRational ht).comp contDiff_id.neg))).sub
    (contDiff_const.mul ((contDiff_positiveRational ht).comp (contDiff_id.sub contDiff_const)))

end Eden.StrangeProof.Direct
