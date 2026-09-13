import EdensConjecture.EmbeddedStrangeProof.PositiveRegularity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

def postFlow (t : ℝ) (p : ℝ × ℝ) : ℝ := transitionPost (p.1, p.2 - p.1 ^ 2 * t)

theorem contDiffAt_postFlow {t : ℝ} {p : ℝ × ℝ} (ha : p.1 ≠ 0) :
    ContDiffAt ℝ 1 (postFlow t) p := by
  exact (contDiffAt_transitionPost (p := (p.1, p.2 - p.1 ^ 2 * t)) ha).comp p
    (contDiffAt_fst.prodMk (contDiffAt_snd.sub ((contDiffAt_fst.pow 2).mul contDiffAt_const)))

theorem contDiffAt_negativeFlow_near_zero {t : ℝ} {p : ℝ × ℝ}
    (ha : 0 < p.1) (hl : -p.1 < p.2) (hr : p.2 < p.1) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => negativeFlow q.1 t q.2) p := by
  have he : ContDiff ℝ 1 (fun q : ℝ × ℝ => Real.exp (-2 * q.1 * t)) := by fun_prop
  apply ((contDiffAt_fst.neg).mul ((contDiffAt_fst.sub contDiffAt_snd).sub
    ((contDiffAt_fst.add contDiffAt_snd).mul he.contDiffAt))).div
    ((contDiffAt_fst.sub contDiffAt_snd).add ((contDiffAt_fst.add contDiffAt_snd).mul he.contDiffAt))
  have hd : 0 < p.1 - p.2 + (p.1 + p.2) * Real.exp (-2 * p.1 * t) :=
    add_pos (sub_pos.mpr hr) (mul_pos (by linarith) (Real.exp_pos _))
  exact hd.ne'

theorem postFlow_zero_eq_negativeFlow (a t : ℝ) (ha : a ≠ 0) :
    postFlow t (a, 0) = negativeFlow a t 0 := by
  rw [postFlow, transitionPost_eq_negativeFlow ha]
  congr 1
  field_simp <;> ring

theorem fderiv_negativeFlow_eq_postFlow {a t : ℝ} (ha : 0 < a) :
    fderiv ℝ (fun q : ℝ × ℝ => negativeFlow q.1 t q.2) (a, 0) =
      fderiv ℝ (postFlow t) (a, 0) := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (a, (0 : ℝ)))
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := (a, (0 : ℝ)))
  have he := ((hf.const_mul (-2)).mul_const t).exp
  have hn := Eden.StrangeProof.hasFDerivAt_real_div
    (hf.neg.mul ((hf.sub hs).sub ((hf.add hs).mul he)))
    ((hf.sub hs).add ((hf.add hs).mul he))
    (by dsimp; positivity)
  have hz := hs.sub ((hf.pow 2).mul_const t)
  have he2 := (Eden.StrangeProof.hasFDerivAt_real_div (hz.const_mul 2) hf ha.ne').exp
  have hp := Eden.StrangeProof.hasFDerivAt_real_div
    (hf.mul (he2.sub_const 1)) (he2.add_const 1) (by dsimp; positivity)
  have hex : 2 * (0 - a ^ 2 * t) / a = -2 * a * t := by field_simp <;> ring
  have hd : a + a * Real.exp (-2 * a * t) ≠ 0 := by positivity
  have hd2 : Real.exp (-2 * a * t) + 1 ≠ 0 := by positivity
  have hne : a ≠ 0 := ha.ne'
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Pi.neg_apply] at hn hp
  unfold negativeFlow postFlow transitionPost
  rw [hn.fderiv, hp.fderiv]
  ext q
  <;> simp [ContinuousLinearMap.comp_apply, Pi.mul_apply, hex, smul_eq_mul]
  <;> field_simp
  <;> ring

theorem contDiffAt_forcedScalarFlow_positive_parameter_zero_initial
    {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => forcedScalarFlow q.1 t q.2) (a, 0) := by
  by_cases ht0 : t = 0
  · subst t
    apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds ha)] with q hq
    exact forcedScalarFlow_zero hq.le q.2
  have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let U : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ -q.1 < q.2 ∧ q.2 < q.1 ∧ q.2 < q.1 ^ 2 * t ∧ q.2 < 1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst.neg continuous_snd).inter
        ((isOpen_lt continuous_snd continuous_fst).inter
          ((isOpen_lt continuous_snd ((continuous_fst.pow 2).mul continuous_const)).inter
            (isOpen_lt continuous_snd continuous_const))))
  have hx : (a, (0 : ℝ)) ∈ U := ⟨ha, by linarith, ha, mul_pos (sq_pos_of_pos ha) htp, by norm_num⟩
  have hc := Eden.StrangeProof.contDiffOn_ite_le_of_matching_derivatives
    (f := fun q : ℝ × ℝ => negativeFlow q.1 t q.2) (g := postFlow t)
    (h := fun q => q.2) hU continuous_snd
    (fun q hq => (contDiffAt_negativeFlow_near_zero hq.1 hq.2.1 hq.2.2.1).contDiffWithinAt)
    (fun q hq => (contDiffAt_postFlow hq.1.ne').contDiffWithinAt)
    (by
      intro q hq hz
      simpa only [← hz] using (postFlow_zero_eq_negativeFlow q.1 t hq.1.ne').symm)
    (by
      intro q hq hz
      simpa only [← hz] using (fderiv_negativeFlow_eq_postFlow (t := t) hq.1))
  apply (hc.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with q hq
  by_cases hv : q.2 ≤ 0
  · simp only [forcedScalarFlow, if_neg hq.1.ne', if_pos hv]
  · have htime : ¬t ≤ q.2 / q.1 ^ 2 := by
      rw [not_le, div_lt_iff₀ (sq_pos_of_pos hq.1)]
      nlinarith [hq.2.2.2.1]
    simp only [forcedScalarFlow, if_neg hq.1.ne', if_neg hv, if_pos hq.2.2.2.2.le,
      if_neg htime, postFlow, transitionPost_eq_negativeFlow hq.1.ne']
    congr 1
    field_simp [hq.1.ne'] <;> ring

end Eden.StrangeProof.Direct
