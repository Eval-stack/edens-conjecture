import EdensConjecture.EmbeddedStrangeProof.Scalar
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

theorem scalarFlow_neg {t u : ℝ} (ht : 0 ≤ t) (hu : u < 0) : scalarFlow t u < 0 := by
  simp only [scalarFlow, if_pos hu]
  exact div_neg_of_neg_of_pos hu (lower_denominator_pos ht hu)

theorem scalarFlow_gt_one {t u : ℝ} (ht : 0 ≤ t) (hu : 1 < u) : 1 < scalarFlow t u := by
  have h0 : ¬u < 0 := by linarith
  simp only [scalarFlow, if_neg h0, if_pos hu]
  have := div_pos (sub_pos.mpr hu) (upper_denominator_pos ht hu)
  linarith

theorem scalarFlow_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (u : ℝ) :
    scalarFlow (s + t) u = scalarFlow s (scalarFlow t u) := by
  by_cases hu0 : u < 0
  · have hv0 := scalarFlow_neg ht hu0
    have hd := (lower_denominator_pos ht hu0).ne'
    have hds := (lower_denominator_pos hs hv0).ne'
    have hdst := (lower_denominator_pos (add_nonneg hs ht) hu0).ne'
    simp only [scalarFlow, if_pos hu0] at hv0 hds ⊢
    rw [if_pos hv0]
    rw [div_div]
    congr 1
    field_simp [hd]
    <;> ring
  by_cases hu1 : 1 < u
  · have hv1 := scalarFlow_gt_one ht hu1
    have hv0 : ¬scalarFlow t u < 0 := by linarith
    have hd := (upper_denominator_pos ht hu1).ne'
    have hds := (upper_denominator_pos hs hv1).ne'
    have hdst := (upper_denominator_pos (add_nonneg hs ht) hu1).ne'
    simp only [scalarFlow, if_neg hu0, if_pos hu1, add_sub_cancel_left] at hds
    simp only [scalarFlow, if_neg hu0, if_pos hu1] at hv1 hv0 ⊢
    rw [if_neg hv0, if_pos hv1]
    simp only [add_sub_cancel_left]
    congr 1
    rw [div_div]
    congr 1
    field_simp [hd]
    <;> ring
  · have hu : u ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hu0, le_of_not_gt hu1⟩
    simp only [scalarFlow_fixed hu]

theorem scalarFlow_bounds {t u : ℝ} (ht : 0 ≤ t) :
    min u 0 ≤ scalarFlow t u ∧ scalarFlow t u ≤ max u 1 := by
  by_cases hu0 : u < 0
  · have hd := lower_denominator_pos ht hu0
    have hl : u ≤ scalarFlow t u := by
      simp only [scalarFlow, if_pos hu0]
      apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg ht (sq_nonneg u)]
    have hh := scalarFlow_neg ht hu0
    exact ⟨(min_le_left _ _).trans hl, hh.le.trans ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _))⟩
  by_cases hu1 : 1 < u
  · have hd := upper_denominator_pos ht hu1
    have hh : scalarFlow t u ≤ u := by
      simp only [scalarFlow, if_neg hu0, if_pos hu1]
      have : (u - 1) / (1 + t * (u - 1)) ≤ u - 1 := by
        apply (div_le_iff₀ hd).mpr
        nlinarith [mul_nonneg ht (sq_nonneg (u - 1))]
      linarith
    exact ⟨(min_le_right _ _).trans ((by norm_num : (0 : ℝ) ≤ 1).trans (scalarFlow_gt_one ht hu1).le),
      hh.trans (le_max_left _ _)⟩
  · rw [scalarFlow_fixed ⟨le_of_not_gt hu0, le_of_not_gt hu1⟩]
    exact ⟨min_le_left _ _, le_max_left _ _⟩

theorem scalarFlow_mem_domain {t u : ℝ} (ht : 0 ≤ t) (hu : u ∈ Ioo (-1 : ℝ) 2) :
    scalarFlow t u ∈ Ioo (-1 : ℝ) 2 := by
  obtain ⟨hl, hh⟩ := scalarFlow_bounds (u := u) ht
  exact ⟨(lt_min hu.1 (by norm_num)).trans_le hl,
    hh.trans_lt (max_lt hu.2 (by norm_num))⟩

theorem scalarFlow_close_to_interval {t : ℝ} (ht : 0 < t) (u : ℝ) :
    ∃ v ∈ Icc (0 : ℝ) 1, |scalarFlow t u - v| ≤ 1 / t := by
  by_cases hu0 : u < 0
  · refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [sub_zero, abs_of_neg (scalarFlow_neg ht.le hu0)]
    simp only [scalarFlow, if_pos hu0]
    rw [← neg_div, div_le_div_iff₀ (lower_denominator_pos ht.le hu0) ht]
    nlinarith
  by_cases hu1 : 1 < u
  · refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [abs_of_pos (sub_pos.mpr (scalarFlow_gt_one ht.le hu1))]
    simp only [scalarFlow, if_neg hu0, if_pos hu1, add_sub_cancel_left]
    rw [div_le_div_iff₀ (upper_denominator_pos ht.le hu1) ht]
    nlinarith
  · have hu : u ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hu0, le_of_not_gt hu1⟩
    refine ⟨u, hu, ?_⟩
    rw [scalarFlow_fixed hu, sub_self, abs_zero]
    positivity

theorem hasDerivAt_scalarFlow {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    HasDerivAt (fun s => scalarFlow s u) (-restoring (scalarFlow t u)) t := by
  by_cases hu0 : u < 0
  · have hd := (lower_denominator_pos ht hu0).ne'
    have hg := (hasDerivAt_const t u).div
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).mul_const u)) hd
    have heq : (fun s => scalarFlow s u) = fun s => u / (1 - s * u) := by
      funext s
      simp only [scalarFlow, if_pos hu0]
    rw [heq, restoring_of_neg (scalarFlow_neg ht hu0)]
    simp only [scalarFlow, if_pos hu0]
    convert! hg using 1 <;> simp [div_pow] <;> ring
  by_cases hu1 : 1 < u
  · have hd := (upper_denominator_pos ht hu1).ne'
    have hg := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_const t (u - 1)).div
      ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).mul_const (u - 1))) hd)
    have heq : (fun s => scalarFlow s u) = fun s => 1 + (u - 1) / (1 + s * (u - 1)) := by
      funext s
      simp only [scalarFlow, if_neg hu0, if_pos hu1]
    rw [heq, restoring_of_gt (scalarFlow_gt_one ht hu1)]
    simp only [scalarFlow, if_neg hu0, if_pos hu1, add_sub_cancel_left]
    convert! hg using 1 <;> simp [div_pow] <;> ring
  · have hu : u ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hu0, le_of_not_gt hu1⟩
    simpa only [scalarFlow_fixed hu, restoring_of_mem hu, neg_zero] using hasDerivAt_const t u

end Eden.StrangeProof.Direct
