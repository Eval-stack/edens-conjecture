import EdensConjecture.EmbeddedStrangeProof.CantorMap
import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter Metric MeasureTheory.Measure
open scoped NNReal ENNReal Topology MeasureTheory

theorem dimH_unitInterval : dimH (Icc (0 : ℝ) 1) = 1 := by
  have h : (interior (Icc (0 : ℝ) 1)).Nonempty := by
    rw [interior_Icc]
    exact ⟨1 / 2, by norm_num, by norm_num⟩
  simpa using Real.dimH_of_nonempty_interior h

theorem cantorSet_dimH_lower : (4 : ENNReal) / 5 ≤ dimH cantorSet := by
  have h := holderOnWith_cantorBinaryMap.dimH_image_le (by norm_num : (0 : ℝ≥0) < 4 / 5)
  rw [cantorBinaryMap_image, dimH_unitInterval] at h
  have hmul := (ENNReal.le_div_iff_mul_le
    (Or.inl (by norm_num : ((4 / 5 : ℝ≥0) : ENNReal) ≠ 0))
    (Or.inl ENNReal.coe_ne_top)).mp h
  simpa using hmul

theorem cantor_cover_ratio_lt_one : 2 * contraction ^ (5 / 6 : ℝ) < 1 := by
  have hc : 0 ≤ contraction := by norm_num [contraction]
  have hp : (contraction ^ (5 / 6 : ℝ)) ^ (6 : ℕ) = contraction ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc]
    norm_num
  apply (pow_lt_pow_iff_left₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1) (by decide : 6 ≠ 0)).mp
  rw [mul_pow, hp, one_pow]
  exact upper_dimension_ratio

def cantorCoverInterval (n : ℕ) (w : Fin n → Bool) : Set ℝ :=
  let p := cantorPrefix (fun j => if h : j < n then w ⟨j, h⟩ else false) n
  Icc p (p + contraction ^ n)

theorem cantorCoverInterval_ediam (n : ℕ) (w : Fin n → Bool) :
    ediam (cantorCoverInterval n w) = ENNReal.ofReal (contraction ^ n) := by
  simp [cantorCoverInterval, Real.ediam_Icc]

theorem cantorCoverInterval_sum (n : ℕ) :
    (∑ w : Fin n → Bool, ediam (cantorCoverInterval n w) ^ (5 / 6 : ℝ)) =
      ENNReal.ofReal ((2 * contraction ^ (5 / 6 : ℝ)) ^ n) := by
  simp only [cantorCoverInterval_ediam, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.ofReal_pow (by norm_num [contraction]),
    ENNReal.ofReal_pow (show 0 ≤ 2 * contraction ^ (5 / 6 : ℝ) from mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num [contraction]) _)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ contraction by norm_num [contraction]) (show (0 : ℝ) ≤ 5 / 6 by norm_num),
    ENNReal.ofReal_ofNat, mul_pow]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  ring

theorem cantorSet_hausdorffMeasure_zero : μH[5 / 6] cantorSet = 0 := by
  have hc : 0 ≤ contraction := by norm_num [contraction]
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (contraction ^ n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc (by norm_num [contraction]))
  have hsum : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 * contraction ^ (5 / 6 : ℝ)) ^ n))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) cantor_cover_ratio_lt_one)
  have h := hausdorffMeasure_le_liminf_sum (5 / 6) cantorSet
    (fun n => ENNReal.ofReal (contraction ^ n)) hr cantorCoverInterval
    (Eventually.of_forall fun n w => (cantorCoverInterval_ediam n w).le)
    (Eventually.of_forall cantorSet_subset_prefix_cover)
  simp_rw [cantorCoverInterval_sum] at h
  rw [hsum.liminf_eq] at h
  exact le_antisymm h bot_le

theorem cantorSet_dimH_upper : dimH cantorSet ≤ (5 : ENNReal) / 6 := by
  have h := dimH_le_of_hausdorffMeasure_ne_top
    (d := (5 / 6 : ℝ≥0)) (s := cantorSet) (by
      norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
      rw [cantorSet_hausdorffMeasure_zero]
      exact ENNReal.zero_ne_top)
  simpa using h

end Eden.StrangeProof.Direct
