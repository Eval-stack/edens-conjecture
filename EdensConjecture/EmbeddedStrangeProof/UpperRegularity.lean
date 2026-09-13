import EdensConjecture.EmbeddedStrangeProof.Removable
import EdensConjecture.EmbeddedStrangeProof.TangentODE

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

def sinSlope (t a : ℝ) : ℝ := dslope (fun x : ℝ => Real.sin (t * x)) 0 a

theorem sinSlope_zero (t : ℝ) : sinSlope t 0 = t := by
  rw [sinSlope, dslope_same]
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul t).sin
  simpa using h.deriv

theorem sinSlope_of_ne (t : ℝ) {a : ℝ} (ha : a ≠ 0) :
    sinSlope t a = Real.sin (t * a) / a := by
  simp [sinSlope, dslope_of_ne _ ha, slope_def_field, div_eq_mul_inv]

theorem contDiff_sinSlope (t : ℝ) : ContDiff ℝ 1 (sinSlope t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  by_cases ha : a = 0
  · subst a
    have he : AnalyticAt ℝ (fun x : ℝ => Real.sin (t * x)) 0 := by fun_prop
    obtain ⟨p, hp⟩ := he
    exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt
  · have heq : sinSlope t =ᶠ[𝓝 a] (fun x : ℝ => Real.sin (t * x) / x) := by
      filter_upwards [eventually_ne_nhds ha] with x hx
      exact sinSlope_of_ne t hx
    exact (((contDiff_const.mul contDiff_id).sin).contDiffAt.div
      contDiffAt_id ha).congr_of_eventuallyEq heq

def regularUpperFlow (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  1 + ((p.2 - 1) * Real.cos (t * p.1) - p.1 ^ 2 * sinSlope t p.1) /
    (Real.cos (t * p.1) + (p.2 - 1) * sinSlope t p.1)

theorem regularUpperFlow_zero_parameter {t v : ℝ} (hv : 1 < v) :
    regularUpperFlow t (0, v) = scalarFlow t v := by
  simp [regularUpperFlow, sinSlope_zero, scalarFlow, not_lt.mpr (by linarith : 0 ≤ v), hv, mul_comm]

theorem contDiffAt_regularUpperFlow {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ}
    (ha : 0 ≤ p.1) (hv : 1 ≤ p.2) (hangle : t * p.1 < Real.pi / 2) :
    ContDiffAt ℝ 1 (regularUpperFlow t) p := by
  have hD : Real.cos (t * p.1) + (p.2 - 1) * sinSlope t p.1 ≠ 0 := by
    have hcos : 0 < Real.cos (t * p.1) := Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos, mul_nonneg ht ha], hangle⟩
    have hs : 0 ≤ sinSlope t p.1 := by
      by_cases hz : p.1 = 0
      · simpa [hz, sinSlope_zero] using ht
      · rw [sinSlope_of_ne t hz]
        exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg ht ha)
          (by linarith [Real.pi_pos])) ha
    exact (add_pos_of_pos_of_nonneg hcos (mul_nonneg (sub_nonneg.mpr hv) hs)).ne'
  have he := (contDiff_sinSlope t).contDiffAt.comp p contDiffAt_fst
  have hc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Real.cos (t * q.1)) p := by fun_prop
  exact contDiffAt_const.add
    ((((contDiffAt_snd.sub contDiffAt_const).mul hc).sub ((contDiffAt_fst.pow 2).mul he)).div
      (hc.add ((contDiffAt_snd.sub contDiffAt_const).mul he)) hD)

theorem regularUpperFlow_eq_tangentFlow {a t v : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (hv : 1 < v) (hangle : t * a < Real.pi / 2) :
    regularUpperFlow t (a, v) = tangentFlow a t v := by
  have hc : Real.cos (Real.arctan ((v - 1) / a)) ≠ 0 := (Real.cos_arctan_pos _).ne'
  have hs : Real.sin (Real.arctan ((v - 1) / a)) =
      ((v - 1) / a) * Real.cos (Real.arctan ((v - 1) / a)) := by
    rw [← Real.tan_mul_cos hc, Real.tan_arctan]
  have hcos : 0 < Real.cos (t * a) := Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, mul_nonneg ht ha.le], hangle⟩
  have hsin : 0 ≤ Real.sin (t * a) := Real.sin_nonneg_of_nonneg_of_le_pi
    (mul_nonneg ht ha.le) (by linarith [Real.pi_pos])
  have hD : Real.cos (t * a) + (v - 1) * (Real.sin (t * a) / a) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hcos (mul_nonneg (sub_nonneg.mpr hv.le) (div_nonneg hsin ha.le))).ne'
  unfold regularUpperFlow tangentFlow
  rw [sinSlope_of_ne t ha.ne', show a * t = t * a by ring,
    Real.tan_eq_sin_div_cos, Real.sin_sub, Real.cos_sub, hs]
  have hd : Real.cos (Real.arctan ((v - 1) / a)) * Real.cos (t * a) +
      ((v - 1) / a * Real.cos (Real.arctan ((v - 1) / a))) * Real.sin (t * a) =
      Real.cos (Real.arctan ((v - 1) / a)) *
        (Real.cos (t * a) + (v - 1) * (Real.sin (t * a) / a)) := by ring
  rw [hd]
  field_simp
  <;> ring

theorem contDiffAt_forcedScalarFlow_upper_zero {t : ℝ} (ht : 0 ≤ t)
    {p : ℝ × ℝ} (hv : 1 < p.2) (hg : gapFunction p.1 = 0) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => forcedScalarFlow (gapFunction q.1) t q.2) p := by
  have hparam : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (gapFunction q.1, q.2)) p :=
    (contDiff_gapFunction.contDiffAt.comp p contDiffAt_fst).prodMk contDiffAt_snd
  have hc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => regularUpperFlow t (gapFunction q.1, q.2)) p := by
    convert! (contDiffAt_regularUpperFlow (p := (gapFunction p.1, p.2)) ht
      (gapFunction_nonneg _) hv.le (by simp [hg, Real.pi_pos])).comp p hparam using 1
  apply hc.congr_of_eventuallyEq
  have hgap : Continuous (fun q : ℝ × ℝ => gapFunction q.1) := contDiff_gapFunction.continuous.comp continuous_fst
  have hsmall : ∀ᶠ q : ℝ × ℝ in 𝓝 p, gapFunction q.1 < q.2 - 1 :=
    hgap.continuousAt.eventually_lt (continuous_snd.sub continuous_const).continuousAt (by simpa [hg] using sub_pos.mpr hv)
  have htime : ∀ᶠ q : ℝ × ℝ in 𝓝 p, t * gapFunction q.1 < Real.arctan 1 :=
    (continuous_const.mul hgap).continuousAt.eventually_lt continuous_const.continuousAt
      (by simp [hg, Real.pi_pos])
  have hangle : ∀ᶠ q : ℝ × ℝ in 𝓝 p, t * gapFunction q.1 < Real.pi / 2 :=
    (continuous_const.mul hgap).continuousAt.eventually_lt continuous_const.continuousAt
      (by simp [hg, Real.pi_pos])
  filter_upwards [hsmall, htime, hangle] with q hq hqt hqa
  have hqv : 1 < q.2 := by linarith [gapFunction_nonneg q.1]
  by_cases hz : gapFunction q.1 = 0
  · simp only [hz, forcedScalarFlow, if_pos rfl]
    exact (regularUpperFlow_zero_parameter hqv).symm
  · have ha : 0 < gapFunction q.1 := lt_of_le_of_ne (gapFunction_nonneg _) (Ne.symm hz)
    have hratio : 1 ≤ (q.2 - 1) / gapFunction q.1 := (le_div_iff₀ ha).mpr (by linarith)
    have hτ : t ≤ Real.arctan ((q.2 - 1) / gapFunction q.1) / gapFunction q.1 := by
      apply (le_div_iff₀ ha).mpr
      exact hqt.le.trans (Real.arctan_le_arctan_iff.mpr hratio)
    simp only [forcedScalarFlow, if_neg hz, if_neg (show ¬q.2 ≤ 0 by linarith),
      if_neg (not_le.mpr hqv), if_pos hτ]
    exact (regularUpperFlow_eq_tangentFlow ha ht hqv hqa).symm

end Eden.StrangeProof.Direct
