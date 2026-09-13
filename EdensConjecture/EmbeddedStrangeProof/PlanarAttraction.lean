import EdensConjecture.EmbeddedStrangeProof.ForcedAttraction
import EdensConjecture.EmbeddedStrangeProof.Geometry

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

theorem interval_near_of_strip {y η : ℝ} (hη : 0 ≤ η) (hl : -η ≤ y) (hh : y ≤ 1 + η) :
    ∃ v ∈ Icc (0 : ℝ) 1, |y - v| ≤ η := by
  by_cases hy0 : y < 0
  · refine ⟨0, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [sub_zero, abs_of_neg hy0]
    linarith
  by_cases hy1 : 1 < y
  · refine ⟨1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [abs_of_pos (sub_pos.mpr hy1)]
    linarith
  · exact ⟨y, ⟨le_of_not_gt hy0, le_of_not_gt hy1⟩, by simpa using hη⟩

theorem planar_close_to_comb {x y δ t : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 2) (hy : y ∈ Ioo (-1 : ℝ) 2)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht : 0 < t) (htinv : 1 / t ≤ δ)
    (htwait : 2 * ((Real.pi + 2) / δ ^ 8) ≤ t) (htrate : 2 / δ ^ 5 ≤ t) :
    ∃ p ∈ comb cantorSet gapFunction,
      |scalarFlow t x - p.1| ≤ δ ∧ |forcedScalarFlow (gapFunction x) t y - p.2| ≤ 2 * δ := by
  by_cases hx0 : x < 0
  · have hg : gapFunction x = 0 := gapFunction_zero_outside (fun h => hx0.not_ge h.1)
    obtain ⟨w, hw, hwy⟩ := scalarFlow_close_to_interval ht y
    obtain ⟨z, hz, hzx⟩ := scalarFlow_close_to_interval ht x
    have hxneg := scalarFlow_neg ht.le hx0
    have hzx' := abs_le.mp hzx
    refine ⟨(0, w), Or.inr ⟨zero_mem_cantorSet, hw⟩, ?_, ?_⟩
    · change |scalarFlow t x - 0| ≤ δ
      rw [sub_zero, abs_of_neg hxneg]
      linarith [hz.1]
    · simpa [hg, forcedScalarFlow] using hwy.trans (by linarith)
  by_cases hx1 : 1 < x
  · have hg : gapFunction x = 0 := gapFunction_zero_outside (fun h => hx1.not_ge h.2)
    obtain ⟨w, hw, hwy⟩ := scalarFlow_close_to_interval ht y
    obtain ⟨z, hz, hzx⟩ := scalarFlow_close_to_interval ht x
    have hxpos := scalarFlow_gt_one ht.le hx1
    have hzx' := abs_le.mp hzx
    refine ⟨(1, w), Or.inr ⟨one_mem_cantorSet, hw⟩, ?_, ?_⟩
    · change |scalarFlow t x - 1| ≤ δ
      rw [abs_of_pos (sub_pos.mpr hxpos)]
      linarith [hz.2]
    · simpa [hg, forcedScalarFlow] using hwy.trans (by linarith)
  have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨le_of_not_gt hx0, le_of_not_gt hx1⟩
  have ha0 := gapFunction_nonneg x
  have ha1 : gapFunction x ≤ 1 := (gapFunction_le x).trans (by norm_num)
  by_cases hsmall : gapFunction x < δ ^ 4
  · obtain ⟨c, hc, hxc⟩ := exists_cantor_near_of_gap_small hxI hδ.le hsmall
    have hδ4 : δ ^ 4 ≤ δ := by
      have hpow : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
      nlinarith [mul_le_mul_of_nonneg_left hpow hδ.le]
    have haδ : gapFunction x ≤ δ := hsmall.le.trans hδ4
    obtain ⟨hl, hh⟩ := forcedScalarFlow_strip (v := y) ha0 ht
    obtain ⟨w, hw, hwy⟩ := interval_near_of_strip (show 0 ≤ gapFunction x + 1 / t by positivity)
      (show -(gapFunction x + 1 / t) ≤ forcedScalarFlow (gapFunction x) t y by linarith)
      (show forcedScalarFlow (gapFunction x) t y ≤ 1 + (gapFunction x + 1 / t) by linarith)
    refine ⟨(c, w), Or.inr ⟨hc, hw⟩, ?_, hwy.trans (by linarith)⟩
    simpa only [scalarFlow_fixed hxI] using hxc.le
  · have hlarge : δ ^ 4 ≤ gapFunction x := le_of_not_gt hsmall
    have hap : 0 < gapFunction x := (pow_pos hδ 4).trans_le hlarge
    have hsq : δ ^ 8 ≤ gapFunction x ^ 2 := by
      have h := pow_le_pow_left₀ (pow_nonneg hδ.le 4) hlarge 2
      simpa only [← pow_mul] using h
    have hwait : 2 * ((Real.pi + 2) / gapFunction x ^ 2) ≤ t := by
      apply le_trans _ htwait
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (by linarith [Real.pi_pos]) (pow_pos hδ 8) hsq
    have hprod : δ ^ 5 ≤ gapFunction x * δ := by
      have h := mul_le_mul_of_nonneg_right hlarge hδ.le
      simpa only [← pow_succ] using h
    have hrate : 2 / (gapFunction x * δ) ≤ t :=
      (div_le_div_of_nonneg_left (by norm_num) (pow_pos hδ 5) hprod).trans htrate
    have hclose := forcedScalarFlow_close_to_graph hap ha1 hy hδ hwait hrate
    refine ⟨(x, -gapFunction x), Or.inl ⟨x, hxI, rfl⟩, ?_, ?_⟩
    · simp only [scalarFlow_fixed hxI, sub_self, abs_zero]
      exact hδ.le
    · simpa only [sub_neg_eq_add] using hclose.trans (by linarith)

def attractionTime (δ : ℝ) : ℝ := 1 / δ + 2 * ((Real.pi + 2) / δ ^ 8) + 2 / δ ^ 5

theorem attractionTime_pos {δ : ℝ} (hδ : 0 < δ) : 0 < attractionTime δ := by
  unfold attractionTime
  have hpi := Real.pi_pos
  positivity

theorem planar_uniform_attraction {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {t : ℝ} (ht : attractionTime δ ≤ t) {x y : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 2) (hy : y ∈ Ioo (-1 : ℝ) 2) :
    ∃ p ∈ comb cantorSet gapFunction,
      |scalarFlow t x - p.1| ≤ δ ∧ |forcedScalarFlow (gapFunction x) t y - p.2| ≤ 2 * δ := by
  have ht0 : 0 < t := (attractionTime_pos hδ).trans_le ht
  have h1 : 0 ≤ 1 / δ := by positivity
  have h2 : 0 ≤ 2 * ((Real.pi + 2) / δ ^ 8) := by have hpi := Real.pi_pos; positivity
  have h3 : 0 ≤ 2 / δ ^ 5 := by positivity
  have htin : 1 / δ ≤ t := by unfold attractionTime at ht; linarith
  have hinv : 1 / t ≤ δ := by
    apply (div_le_iff₀ ht0).mpr
    have h := (div_le_iff₀ hδ).mp htin
    nlinarith
  apply planar_close_to_comb hx hy hδ hδ1 ht0 hinv
  · unfold attractionTime at ht
    linarith
  · unfold attractionTime at ht
    linarith

end Eden.StrangeProof.Direct
