import EdensConjecture.EmbeddedStrangeProof.NegativeFlow

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

theorem tangentBranch_bounds {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : 1 < v)
    (hτ : t ≤ Real.arctan ((v - 1) / a) / a) :
    1 ≤ 1 + a * Real.tan (Real.arctan ((v - 1) / a) - a * t) ∧
      1 + a * Real.tan (Real.arctan ((v - 1) / a) - a * t) ≤ v := by
  have hθ0 : 0 ≤ Real.arctan ((v - 1) / a) :=
    Real.arctan_nonneg.mpr (div_nonneg (sub_nonneg.mpr hv.le) ha.le)
  have hθ1 := Real.arctan_lt_pi_div_two ((v - 1) / a)
  have htime := (le_div_iff₀ ha).mp hτ
  have hz0 : 0 ≤ Real.arctan ((v - 1) / a) - a * t := by nlinarith
  have hzθ : Real.arctan ((v - 1) / a) - a * t ≤ Real.arctan ((v - 1) / a) := by nlinarith
  have ht0 := Real.tan_nonneg_of_nonneg_of_le_pi_div_two hz0 (hzθ.trans hθ1.le)
  have htan := Real.strictMonoOn_tan.monotoneOn
    (show Real.arctan ((v - 1) / a) - a * t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], hzθ.trans_lt hθ1⟩)
    (show Real.arctan ((v - 1) / a) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], hθ1⟩) hzθ
  rw [Real.tan_arctan] at htan
  have hm := mul_le_mul_of_nonneg_left htan ha.le
  have heq : a * ((v - 1) / a) = v - 1 := by field_simp
  rw [heq] at hm
  exact ⟨by nlinarith, by linarith⟩

theorem linearBranch_bounds {a t v : ℝ} (ha : 0 < a) (ht : 0 ≤ t) (hv : 0 ≤ v)
    (hτ : t ≤ v / a ^ 2) : 0 ≤ v - a ^ 2 * t ∧ v - a ^ 2 * t ≤ v := by
  have h := (le_div_iff₀ (sq_pos_of_pos ha)).mp hτ
  constructor <;> nlinarith [mul_nonneg (sq_nonneg a) ht]

theorem forcedScalarFlow_bounds {a t v : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    min v (-a) ≤ forcedScalarFlow a t v ∧ forcedScalarFlow a t v ≤ max v 1 := by
  by_cases hz : a = 0
  · subst a
    simpa [forcedScalarFlow] using scalarFlow_bounds (u := v) ht
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  by_cases hv0 : v ≤ 0
  · simp only [forcedScalarFlow, if_neg hz, if_pos hv0]
    exact ⟨negativeFlow_ge_min hap ht hv0,
      (negativeFlow_nonpos hap ht hv0).trans ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _))⟩
  have hvp : 0 < v := lt_of_not_ge hv0
  by_cases hv1 : v ≤ 1
  · simp only [forcedScalarFlow, if_neg hz, if_neg hv0, if_pos hv1]
    split_ifs with hτ
    · obtain ⟨hl, hh⟩ := linearBranch_bounds hap ht hvp.le hτ
      exact ⟨(min_le_right _ _).trans ((neg_nonpos.mpr ha).trans hl), hh.trans (le_max_left _ _)⟩
    · have hs : 0 ≤ t - v / a ^ 2 := sub_nonneg.mpr (le_of_not_ge hτ)
      have hl := negativeFlow_ge_min hap hs (le_rfl : (0 : ℝ) ≤ 0)
      have hh := negativeFlow_nonpos hap hs (le_rfl : (0 : ℝ) ≤ 0)
      rw [min_eq_right (neg_nonpos.mpr ha)] at hl
      exact ⟨(min_le_right _ _).trans hl, hh.trans ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _))⟩
  · have hvgt : 1 < v := lt_of_not_ge hv1
    simp only [forcedScalarFlow, if_neg hz, if_neg hv0, if_neg hv1]
    split_ifs with hτ hτ1
    · obtain ⟨hl, hh⟩ := tangentBranch_bounds hap ht hvgt hτ
      exact ⟨(min_le_right _ _).trans (by linarith), hh.trans (le_max_left _ _)⟩
    · have hs : 0 ≤ t - Real.arctan ((v - 1) / a) / a := sub_nonneg.mpr (le_of_not_ge hτ)
      have hstime : t - Real.arctan ((v - 1) / a) / a ≤ 1 / a ^ 2 := by linarith
      obtain ⟨hl, hh⟩ := linearBranch_bounds hap hs (by norm_num : (0 : ℝ) ≤ 1) hstime
      exact ⟨(min_le_right _ _).trans ((neg_nonpos.mpr ha).trans hl), hh.trans (le_max_right _ _)⟩
    · have hs : 0 ≤ t - Real.arctan ((v - 1) / a) / a - 1 / a ^ 2 := by linarith
      have hl := negativeFlow_ge_min hap hs (le_rfl : (0 : ℝ) ≤ 0)
      have hh := negativeFlow_nonpos hap hs (le_rfl : (0 : ℝ) ≤ 0)
      rw [min_eq_right (neg_nonpos.mpr ha)] at hl
      exact ⟨(min_le_right _ _).trans hl, hh.trans ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _))⟩

theorem forcedScalarFlow_mem_domain {a t v : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (ht : 0 ≤ t) (hv : v ∈ Ioo (-1 : ℝ) 2) : forcedScalarFlow a t v ∈ Ioo (-1 : ℝ) 2 := by
  obtain ⟨hl, hh⟩ := forcedScalarFlow_bounds (v := v) ha ht
  exact ⟨(lt_min hv.1 (by linarith)).trans_le hl, hh.trans_lt (max_lt hv.2 (by norm_num))⟩

end Eden.StrangeProof.Direct
