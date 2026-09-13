import EdensConjecture.EmbeddedStrangeProof.ForcedBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

theorem tangentBranch_le_one_add_inv {a t v : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hτ : t ≤ Real.arctan ((v - 1) / a) / a) :
    1 + a * Real.tan (Real.arctan ((v - 1) / a) - a * t) ≤ 1 + 1 / t := by
  let z := Real.arctan ((v - 1) / a) - a * t
  have hz0 : 0 ≤ z := by have h := (le_div_iff₀ ha).mp hτ; dsimp [z]; nlinarith
  have hz1 : z < Real.pi / 2 := by
    have h := Real.arctan_lt_pi_div_two ((v - 1) / a)
    dsimp [z]
    nlinarith
  have hprod : a * Real.tan z * t ≤ 1 := by
    by_cases hz : z = 0
    · simp [hz]
    have hzp : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz)
    have htan := Real.tan_pos_of_pos_of_lt_pi_div_two hzp hz1
    have hq := Real.le_tan (sub_nonneg.mpr hz1.le) (show Real.pi / 2 - z < Real.pi / 2 by linarith)
    rw [Real.tan_pi_div_two_sub] at hq
    have hm := mul_le_mul_of_nonneg_right hq htan.le
    rw [inv_mul_cancel₀ htan.ne'] at hm
    have htime : a * t ≤ Real.pi / 2 - z := by
      have h := Real.arctan_lt_pi_div_two ((v - 1) / a)
      dsimp [z]
      linarith
    have hh := mul_le_mul_of_nonneg_right htime htan.le
    nlinarith
  have h := (le_div_iff₀ ht).mpr hprod
  dsimp [z] at h
  linarith

theorem forcedScalarFlow_strip {a t v : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    -a - 1 / t ≤ forcedScalarFlow a t v ∧ forcedScalarFlow a t v ≤ 1 + 1 / t := by
  have hi : 0 ≤ 1 / t := by positivity
  by_cases hz : a = 0
  · subst a
    obtain ⟨w, hw, hh⟩ := scalarFlow_close_to_interval ht v
    have habs := abs_le.mp hh
    simp only [forcedScalarFlow, ite_true, neg_zero, zero_sub]
    constructor <;> linarith [hw.1, hw.2]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  constructor
  · by_cases hv : v ≤ 0
    · simpa only [forcedScalarFlow, if_neg hz, if_pos hv] using negativeFlow_ge_parameter_sub_inv hap ht hv
    · have h := (forcedScalarFlow_bounds (v := v) ha ht.le).1
      rw [min_eq_right (show -a ≤ v by linarith)] at h
      linarith

  · by_cases hv1 : v ≤ 1
    · have h := (forcedScalarFlow_bounds (v := v) ha ht.le).2
      rw [max_eq_right hv1] at h
      linarith
    have hv0 : ¬v ≤ 0 := by linarith
    simp only [forcedScalarFlow, if_neg hz, if_neg hv0, if_neg hv1]
    split_ifs with hτ hτ1
    · exact tangentBranch_le_one_add_inv hap ht hτ
    · have hs : 0 ≤ t - Real.arctan ((v - 1) / a) / a := sub_nonneg.mpr (le_of_not_ge hτ)
      have hh := mul_nonneg (sq_nonneg a) hs
      linarith
    · have hs : 0 ≤ t - Real.arctan ((v - 1) / a) / a - 1 / a ^ 2 := by linarith
      have hh := negativeFlow_nonpos hap hs (le_rfl : (0 : ℝ) ≤ 0)
      linarith

theorem transitTime_le {a v : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hv : 1 < v) :
    Real.arctan ((v - 1) / a) / a + 1 / a ^ 2 ≤ (Real.pi + 2) / a ^ 2 := by
  have hθ0 : 0 ≤ Real.arctan ((v - 1) / a) :=
    Real.arctan_nonneg.mpr (div_nonneg (by linarith) ha.le)
  have hθ1 := Real.arctan_lt_pi_div_two ((v - 1) / a)
  have hm := mul_le_mul_of_nonneg_left ha1 hθ0
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  have heq : (Real.arctan ((v - 1) / a) / a + 1 / a ^ 2) * a ^ 2 =
      Real.arctan ((v - 1) / a) * a + 1 := by field_simp
  rw [heq]
  nlinarith [Real.pi_pos]

theorem forcedScalarFlow_late_branch {a t v : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hv : v ∈ Ioo (-1 : ℝ) 2) (ht : 2 * ((Real.pi + 2) / a ^ 2) ≤ t) :
    ∃ s w : ℝ, t / 2 ≤ s ∧ w ∈ Icc (-1 : ℝ) 0 ∧ forcedScalarFlow a t v = negativeFlow a s w := by
  have hwait : 0 < (Real.pi + 2) / a ^ 2 := div_pos (by linarith [Real.pi_pos]) (sq_pos_of_pos ha)
  have ht0 : 0 ≤ t := by linarith
  have hone : 1 / a ^ 2 ≤ (Real.pi + 2) / a ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg a)
    linarith [Real.pi_pos]
  by_cases hv0 : v ≤ 0
  · exact ⟨t, v, by linarith, ⟨hv.1.le, hv0⟩, by simp only [forcedScalarFlow, if_neg ha.ne', if_pos hv0]⟩
  by_cases hv1 : v ≤ 1
  · have htrans : v / a ^ 2 ≤ (Real.pi + 2) / a ^ 2 :=
      (div_le_div_of_nonneg_right hv1 (sq_nonneg a)).trans hone
    have hτ : ¬t ≤ v / a ^ 2 := by linarith
    refine ⟨t - v / a ^ 2, 0, by linarith, ⟨by norm_num, le_rfl⟩, ?_⟩
    simp only [forcedScalarFlow, if_neg ha.ne', if_neg hv0, if_pos hv1, if_neg hτ]
  · have htrans := transitTime_le ha ha1 (lt_of_not_ge hv1)
    have hτ1 : ¬t ≤ Real.arctan ((v - 1) / a) / a + 1 / a ^ 2 := by linarith
    have hτ : ¬t ≤ Real.arctan ((v - 1) / a) / a := by
      have hi : 0 ≤ 1 / a ^ 2 := by positivity
      linarith
    refine ⟨t - Real.arctan ((v - 1) / a) / a - 1 / a ^ 2, 0, by linarith,
      ⟨by norm_num, le_rfl⟩, ?_⟩
    simp only [forcedScalarFlow, if_neg ha.ne', if_neg hv0, if_neg hv1, if_neg hτ, if_neg hτ1]

theorem forcedScalarFlow_close_to_graph {a t v ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hv : v ∈ Ioo (-1 : ℝ) 2) (hε : 0 < ε)
    (ht : 2 * ((Real.pi + 2) / a ^ 2) ≤ t) (htε : 2 / (a * ε) ≤ t) :
    |forcedScalarFlow a t v + a| ≤ ε := by
  have hwait : 0 < (Real.pi + 2) / a ^ 2 := div_pos (by linarith [Real.pi_pos]) (sq_pos_of_pos ha)
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨s, w, hs, hw, heq⟩ := forcedScalarFlow_late_branch ha ha1 hv ht
  rw [heq]
  have herr := negativeFlow_error_bound (t := s) ha (by linarith) hw.2
  have hwabs : |a + w| ≤ 1 := abs_le.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hexp : Real.exp (-2 * a * s) ≤ Real.exp (-(a * t)) := Real.exp_le_exp.mpr (by nlinarith)
  have hbound : |negativeFlow a s w + a| ≤ 2 * Real.exp (-(a * t)) := by
    exact herr.trans (mul_le_mul (by linarith) hexp (Real.exp_pos _).le (by norm_num))
  apply hbound.trans
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have he := Real.add_one_le_exp (a * t)
  have hprod := (div_le_iff₀ (mul_pos ha hε)).mp htε
  have hm := mul_le_mul_of_nonneg_left he hε.le
  nlinarith
end Eden.StrangeProof.Direct
