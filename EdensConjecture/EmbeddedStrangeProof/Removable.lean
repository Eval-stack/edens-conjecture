import EdensConjecture.EmbeddedStrangeProof.Attraction
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
namespace Eden.StrangeProof.Direct
open Filter
open scoped Topology

def expSlope (t a : ℝ) : ℝ := dslope (fun x : ℝ => Real.exp (-2 * t * x)) 0 a

theorem expSlope_zero (t : ℝ) : expSlope t 0 = -2 * t := by
  rw [expSlope, dslope_same]
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul (-2 * t)).exp
  simpa using h.deriv

theorem expSlope_of_ne (t : ℝ) {a : ℝ} (ha : a ≠ 0) :
    expSlope t a = (Real.exp (-2 * t * a) - 1) / a := by
  simp [expSlope, dslope_of_ne _ ha, slope_def_field, div_eq_mul_inv]

theorem contDiff_expSlope (t : ℝ) : ContDiff ℝ 1 (expSlope t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro a
  by_cases ha : a = 0
  · subst a
    have he : AnalyticAt ℝ (fun x : ℝ => Real.exp (-2 * t * x)) 0 := by fun_prop
    obtain ⟨p, hp⟩ := he
    exact hp.has_fpower_series_dslope_fslope.analyticAt.contDiffAt
  · have heq : expSlope t =ᶠ[𝓝 a] (fun x : ℝ => (Real.exp (-2 * t * x) - 1) / x) := by
      filter_upwards [eventually_ne_nhds ha] with x hx
      exact expSlope_of_ne t hx
    exact (((contDiff_const.mul contDiff_id).exp.sub contDiff_const).contDiffAt.div
      contDiffAt_id ha).congr_of_eventuallyEq heq

/-- A nonsingular expression for the Riccati branch, including zero forcing. -/
def regularNegativeFlow (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  (2 * p.2 + p.1 * (p.1 + p.2) * expSlope t p.1) /
    (2 + (p.1 + p.2) * expSlope t p.1)

theorem regularNegativeFlow_zero_parameter {t v : ℝ} (hv : v < 0) :
    regularNegativeFlow t (0, v) = scalarFlow t v := by
  simp only [regularNegativeFlow, expSlope_zero, zero_add, zero_mul, add_zero,
    scalarFlow, if_pos hv]
  have he : 2 + v * (-2 * t) = 2 * (1 - t * v) := by ring
  rw [he, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

theorem regularNegativeFlow_eq {t a v : ℝ} (ha : a ≠ 0) :
    regularNegativeFlow t (a, v) = negativeFlow a t v := by
  rw [regularNegativeFlow, expSlope_of_ne t ha]
  have he : -2 * t * a = -2 * a * t := by ring
  rw [he]
  unfold negativeFlow
  have hD : 2 + (a + v) * ((Real.exp (-2 * a * t) - 1) / a) =
      ((a - v) + (a + v) * Real.exp (-2 * a * t)) / a := by field_simp; ring
  have hN : 2 * v + a * (a + v) * ((Real.exp (-2 * a * t) - 1) / a) =
      -((a - v) - (a + v) * Real.exp (-2 * a * t)) := by field_simp; ring
  rw [hD, hN, div_div_eq_mul_div]
  congr 1
  ring

theorem contDiffAt_regularNegativeFlow {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ}
    (ha : 0 ≤ p.1) (hv : p.2 ≤ 0) : ContDiffAt ℝ 1 (regularNegativeFlow t) p := by
  have hD : 2 + (p.1 + p.2) * expSlope t p.1 ≠ 0 := by
    by_cases hz : p.1 = 0
    · rw [hz, expSlope_zero, zero_add]
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hv ht]
    · have hp : 0 < p.1 := lt_of_le_of_ne ha (Ne.symm hz)
      have he : -2 * t * p.1 = -2 * p.1 * t := by ring
      rw [expSlope_of_ne t hz, he]
      have hD := negativeFlow_denominator_pos hp ht hv
      have heq : 2 + (p.1 + p.2) * ((Real.exp (-2 * p.1 * t) - 1) / p.1) =
          ((p.1 - p.2) + (p.1 + p.2) * Real.exp (-2 * p.1 * t)) / p.1 := by
        field_simp; ring
      rw [heq]
      exact (div_pos hD hp).ne'
  have he := (contDiff_expSlope t).contDiffAt.comp p contDiffAt_fst
  exact ((contDiffAt_const.mul contDiffAt_snd).add
    ((contDiffAt_fst.mul (contDiffAt_fst.add contDiffAt_snd)).mul he)).div
      (contDiffAt_const.add ((contDiffAt_fst.add contDiffAt_snd).mul he)) hD

theorem contDiffAt_forcedScalarFlow_negative {t : ℝ} (ht : 0 ≤ t)
    {p : ℝ × ℝ} (hv : p.2 < 0) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => forcedScalarFlow (gapFunction q.1) t q.2) p := by
  have hparam : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (gapFunction q.1, q.2)) p := by
    exact (contDiff_gapFunction.contDiffAt.comp p contDiffAt_fst).prodMk contDiffAt_snd
  have hc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => regularNegativeFlow t (gapFunction q.1, q.2)) p := by
    convert! (contDiffAt_regularNegativeFlow (p := (gapFunction p.1, p.2)) ht
      (gapFunction_nonneg p.1) hv.le).comp p hparam using 1
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt.eventually (Iio_mem_nhds hv)] with q hq
  have hq0 : q.2 < 0 := hq
  by_cases ha : gapFunction q.1 = 0
  · simp only [ha, forcedScalarFlow, if_pos rfl]
    exact (regularNegativeFlow_zero_parameter hq0).symm
  · simp only [forcedScalarFlow, if_neg ha, if_pos hq0.le]
    exact (regularNegativeFlow_eq ha).symm

theorem contDiffAt_forcedScalarFlow_middle {t : ℝ} {p : ℝ × ℝ}
    (hv0 : 0 < p.2) (hv1 : p.2 < 1)
    (ht : t * gapFunction p.1 ^ 2 < p.2) :
    ContDiffAt ℝ 1 (fun q : ℝ × ℝ => forcedScalarFlow (gapFunction q.1) t q.2) p := by
  have hc : ContDiff ℝ 1 (fun q : ℝ × ℝ => q.2 - gapFunction q.1 ^ 2 * t) :=
    contDiff_snd.sub (((contDiff_gapFunction.comp contDiff_fst).pow 2).mul contDiff_const)
  apply hc.contDiffAt.congr_of_eventuallyEq
  have htime : ∀ᶠ q : ℝ × ℝ in 𝓝 p, t * gapFunction q.1 ^ 2 < q.2 :=
    (continuous_const.mul ((contDiff_gapFunction.continuous.comp continuous_fst).pow 2)).continuousAt.eventually_lt
      continuous_snd.continuousAt ht
  filter_upwards [htime, continuous_snd.continuousAt.eventually (Ioi_mem_nhds hv0),
    continuous_snd.continuousAt.eventually (Iio_mem_nhds hv1)] with q hqt hq0 hq1
  have h0 : 0 < q.2 := hq0
  have h1 : q.2 < 1 := hq1
  by_cases ha : gapFunction q.1 = 0
  · simp [forcedScalarFlow, ha, scalarFlow_fixed ⟨h0.le, h1.le⟩]
  · have hsq : 0 < gapFunction q.1 ^ 2 := sq_pos_of_ne_zero ha
    have hle : t ≤ q.2 / gapFunction q.1 ^ 2 := (le_div_iff₀ hsq).mpr hqt.le
    simp only [forcedScalarFlow, if_neg ha, if_neg (not_le.mpr h0), if_pos h1.le, if_pos hle]

end Eden.StrangeProof.Direct
