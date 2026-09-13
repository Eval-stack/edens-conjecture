import EdensConjecture.EmbeddedStrangeProof.MiddleRegularity
import EdensConjecture.EmbeddedStrangeProof.ScaledGlue
import EdensConjecture.EmbeddedStrangeProof.TangentODE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

theorem scaledClamp_of_nonpos {ψ : ℝ → ℝ} (hψ : ψ 0 = 0) (a : ℝ) {z : ℝ} (hz : z ≤ 0) :
    scaledClamp ψ (a, z) = z := by
  by_cases h : 0 ≤ z
  · have he : z = 0 := le_antisymm hz h
    simp [scaledClamp, scaledMap, he, hψ]
  · exact if_neg h

theorem middleClamp_of_nonneg (a : ℝ) {z : ℝ} (hz : 0 ≤ z) : middleClamp (a, z) = z := if_pos hz

def positiveFlow (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  middleClamp (p.1, 1 + scaledClamp Real.tan
    (p.1, scaledClamp Real.arctan (p.1, p.2 - 1) - p.1 ^ 2 * t))

theorem atanClamp_lt {a z : ℝ} (ha : 0 < a) :
    scaledClamp Real.arctan (a, z) < (Real.pi / 2) * a := by
  by_cases hz : 0 ≤ z
  · simp only [scaledClamp, if_pos hz, scaledMap]
    nlinarith [Real.arctan_lt_pi_div_two (z / a)]
  · rw [scaledClamp_of_nonpos Real.arctan_zero a (le_of_not_ge hz)]
    nlinarith [Real.pi_pos]

theorem contDiffAt_positiveFlow {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ} (ha : 0 < p.1) :
    ContDiffAt ℝ 1 (positiveFlow t) p := by
  have hinput : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (q.1, q.2 - 1)) p := by fun_prop
  have hatan := (contDiffOn_atanClamp.contDiffAt (x := (p.1, p.2 - 1))
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ha)).comp p hinput
  have hz : ContDiffAt ℝ 1 (fun q : ℝ × ℝ =>
      (q.1, scaledClamp Real.arctan (q.1, q.2 - 1) - q.1 ^ 2 * t)) p :=
    contDiffAt_fst.prodMk (hatan.sub ((contDiffAt_fst.pow 2).mul contDiffAt_const))
  have hangle : scaledClamp Real.arctan (p.1, p.2 - 1) - p.1 ^ 2 * t < (Real.pi / 2) * p.1 := by
    have h := atanClamp_lt (z := p.2 - 1) ha
    nlinarith [mul_nonneg (sq_nonneg p.1) ht]
  have htan := (contDiffAt_tanClamp
    (p := (p.1, scaledClamp Real.arctan (p.1, p.2 - 1) - p.1 ^ 2 * t)) ha hangle).comp p hz
  have hout : ContDiffAt ℝ 1 (fun q : ℝ × ℝ =>
      (q.1, 1 + scaledClamp Real.tan (q.1, scaledClamp Real.arctan (q.1, q.2 - 1) - q.1 ^ 2 * t))) p :=
    contDiffAt_fst.prodMk (contDiffAt_const.add htan)
  convert! (contDiffOn_middleClamp.contDiffAt (x := (p.1, 1 + scaledClamp Real.tan
    (p.1, scaledClamp Real.arctan (p.1, p.2 - 1) - p.1 ^ 2 * t)))
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ha)).comp p hout using 1

theorem positiveFlow_eq_forcedScalarFlow {a t v : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (hv : 0 < v) : positiveFlow t (a, v) = forcedScalarFlow a t v := by
  by_cases hv1 : v ≤ 1
  · have hz : v - 1 - a ^ 2 * t ≤ 0 := by nlinarith [mul_nonneg (sq_nonneg a) ht]
    simp only [positiveFlow, scaledClamp_of_nonpos Real.arctan_zero a (sub_nonpos.mpr hv1),
      scaledClamp_of_nonpos Real.tan_zero a hz]
    rw [show 1 + (v - 1 - a ^ 2 * t) = v - a ^ 2 * t by ring,
      ← middleFlow_eq_middleClamp ha]
    simp only [forcedScalarFlow, if_neg ha.ne', if_neg (not_le.mpr hv), if_pos hv1, middleFlow]
  · have hvgt : 1 < v := lt_of_not_ge hv1
    let τ := Real.arctan ((v - 1) / a) / a
    have hA : a * Real.arctan ((v - 1) / a) = a ^ 2 * τ := by dsimp [τ]; field_simp <;> ring
    have hinput : scaledClamp Real.arctan (a, v - 1) = a * Real.arctan ((v - 1) / a) := by
      simp only [scaledClamp, if_pos (sub_nonneg.mpr hvgt.le), scaledMap]
    rw [forcedScalarFlow_eq_upperFlow ha hvgt]
    by_cases htime : t ≤ τ
    · have hz : 0 ≤ a * Real.arctan ((v - 1) / a) - a ^ 2 * t := by
        rw [hA]
        nlinarith [sq_pos_of_pos ha]
      have harg : (a * Real.arctan ((v - 1) / a) - a ^ 2 * t) / a =
          Real.arctan ((v - 1) / a) - a * t := by field_simp <;> ring
      unfold positiveFlow
      rw [hinput]
      simp only [scaledClamp, if_pos hz, scaledMap, harg]
      rw [middleClamp_of_nonneg a ((by norm_num : (0 : ℝ) ≤ 1).trans (tangentBranch_bounds ha ht hvgt htime).1)]
      simp only [upperFlow, if_pos (show t ≤ Real.arctan ((v - 1) / a) / a from htime), tangentFlow]
    · have hz : a * Real.arctan ((v - 1) / a) - a ^ 2 * t ≤ 0 := by
        rw [hA]
        nlinarith [sq_pos_of_pos ha, lt_of_not_ge htime]
      simp only [positiveFlow, hinput, scaledClamp_of_nonpos Real.tan_zero a hz,
        upperFlow, if_neg (show ¬t ≤ Real.arctan ((v - 1) / a) / a from htime)]
      rw [middleFlow_eq_middleClamp ha, hA]
      congr 2
      ring

theorem contDiffAt_forcedScalarFlow_positive_parameter_positive_initial
    {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ} (ha : 0 < p.1) (hv : 0 < p.2) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => forcedScalarFlow q.1 t q.2) p := by
  apply (contDiffAt_positiveFlow ht ha).congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds ha),
    continuous_snd.continuousAt.eventually (Ioi_mem_nhds hv)] with q hqa hqv
  exact (positiveFlow_eq_forcedScalarFlow hqa ht hqv).symm

end Eden.StrangeProof.Direct
