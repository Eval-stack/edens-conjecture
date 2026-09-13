import EdensConjecture.EmbeddedStrangeProof.ForcedODE
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

def tangentFlow (a t v : ℝ) : ℝ :=
  1 + a * Real.tan (Real.arctan ((v - 1) / a) - a * t)

theorem restoring_of_ge_one {u : ℝ} (hu : 1 ≤ u) : restoring u = (u - 1) ^ 2 := by
  simp [restoring, max_eq_left (sub_nonneg.mpr hu),
    max_eq_right (show -u ≤ 0 by linarith)]

theorem hasDerivAt_tangentFlow {a t v : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (hv : 1 < v)
    (hτ : t ≤ Real.arctan ((v - 1) / a) / a) :
    HasDerivAt (fun s => tangentFlow a s v)
      (-a ^ 2 - restoring (tangentFlow a t v)) t := by
  let z := Real.arctan ((v - 1) / a) - a * t
  have hz0 : 0 ≤ z := by
    have := (le_div_iff₀ ha).mp hτ
    dsimp [z]
    nlinarith
  have hz1 : z < Real.pi / 2 := by
    have := Real.arctan_lt_pi_div_two ((v - 1) / a)
    dsimp [z]
    nlinarith [mul_nonneg ha.le ht]
  have hc : Real.cos z ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hz1⟩).ne'
  have hsec : 1 / Real.cos z ^ 2 = 1 + Real.tan z ^ 2 := by
    apply (div_eq_iff (pow_ne_zero 2 hc)).mpr
    exact (Real.one_add_tan_sq_mul_cos_sq_eq_one hc).symm
  have hd := ((Real.hasDerivAt_tan hc).comp t
    ((hasDerivAt_const t (Real.arctan ((v - 1) / a))).sub
      ((hasDerivAt_id t).const_mul a))).const_mul a
  have h := (hasDerivAt_const t (1 : ℝ)).add hd
  have hr := restoring_of_ge_one (tangentBranch_bounds ha ht hv hτ).1
  change restoring (tangentFlow a t v) = _ at hr
  rw [hr]
  convert! h using 1
  simp only [tangentFlow, Pi.add_apply, id_eq, mul_one, sub_zero, zero_sub, zero_add]
  change -a ^ 2 - (1 + a * Real.tan z - 1) ^ 2 = a * ((1 / Real.cos z ^ 2) * -a)
  rw [hsec]
  ring

def upperFlow (a t v : ℝ) : ℝ :=
  let τ := Real.arctan ((v - 1) / a) / a
  if t ≤ τ then tangentFlow a t v else middleFlow a (t - τ) 1

theorem tangentFlow_transition {a v : ℝ} (ha : 0 < a) :
    tangentFlow a (Real.arctan ((v - 1) / a) / a) v = 1 := by
  have h : a * (Real.arctan ((v - 1) / a) / a) = Real.arctan ((v - 1) / a) := by
    field_simp
  simp [tangentFlow, h]

theorem middleFlow_zero {a v : ℝ} (ha : 0 < a) (hv : 0 ≤ v) : middleFlow a 0 v = v := by
  simp [middleFlow, div_nonneg hv (sq_nonneg a)]

theorem hasDerivAt_upperFlow {a t v : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (hv : 1 < v) :
    HasDerivAt (fun s => upperFlow a s v)
      (-a ^ 2 - restoring (upperFlow a t v)) t := by
  let τ := Real.arctan ((v - 1) / a) / a
  have hτ0 : 0 ≤ τ := div_nonneg
    (Real.arctan_nonneg.mpr (div_nonneg (sub_nonneg.mpr hv.le) ha.le)) ha.le
  have hone : (1 : ℝ) ∈ Icc 0 1 := ⟨by norm_num, le_rfl⟩
  rcases lt_trichotomy t τ with hlt | heq | hgt
  · have he : (fun s => upperFlow a s v) =ᶠ[𝓝 t] (fun s => tangentFlow a s v) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      exact if_pos (le_of_lt hs)
    simpa only [upperFlow, if_pos (show t ≤ Real.arctan ((v - 1) / a) / a from hlt.le)] using
      (hasDerivAt_tangentFlow ha ht hv hlt.le).congr_of_eventuallyEq he
  · subst t
    have hm : HasDerivAt (fun s => middleFlow a s 1) (-a ^ 2) (τ - τ) := by
      simpa [middleFlow_zero ha (by norm_num : (0 : ℝ) ≤ 1), restoring_of_mem hone] using
        hasDerivAt_middleFlow ha (le_refl 0) hone
    have hmd := hm.comp (h := fun s => s - τ) τ ((hasDerivAt_id τ).sub_const τ)
    have htd : HasDerivAt (fun s => tangentFlow a s v) (-a ^ 2) τ := by
      simpa [τ, tangentFlow_transition ha, restoring_of_mem hone] using
        hasDerivAt_tangentFlow ha hτ0 hv (le_refl τ)
    have hg := hasDerivAt_glue htd (by simpa using hmd)
      (by simp [τ, tangentFlow_transition ha, middleFlow_zero ha (by norm_num : (0 : ℝ) ≤ 1)])
    simpa [upperFlow, τ, tangentFlow_transition ha, restoring_of_mem hone] using hg
  · have hn := (hasDerivAt_middleFlow ha (sub_nonneg.mpr hgt.le) hone).comp t
      ((hasDerivAt_id t).sub_const τ)
    have he : (fun s => upperFlow a s v) =ᶠ[𝓝 t] (fun s => middleFlow a (s - τ) 1) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      exact if_neg (not_le.mpr hs)
    simpa only [upperFlow, if_neg (show ¬t ≤ Real.arctan ((v - 1) / a) / a from not_le.mpr hgt), mul_one] using
      hn.congr_of_eventuallyEq he

theorem forcedScalarFlow_eq_upperFlow {a v : ℝ} (ha : 0 < a) (hv : 1 < v) (t : ℝ) :
    forcedScalarFlow a t v = upperFlow a t v := by
  simp only [forcedScalarFlow, if_neg ha.ne', if_neg (show ¬v ≤ 0 by linarith),
    if_neg (not_le.mpr hv), upperFlow, tangentFlow, middleFlow]
  split_ifs <;> first | rfl | (exfalso; linarith)

theorem hasDerivAt_forcedScalarFlow {a t v : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    HasDerivAt (fun s => forcedScalarFlow a s v)
      (-a ^ 2 - restoring (forcedScalarFlow a t v)) t := by
  by_cases hz : a = 0
  · subst a
    simpa [forcedScalarFlow] using hasDerivAt_scalarFlow ht (u := v)
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
  by_cases hv0 : v ≤ 0
  · simpa only [forcedScalarFlow, if_neg hz, if_pos hv0] using
      hasDerivAt_negativeFlow_ode hap ht hv0
  by_cases hv1 : v ≤ 1
  · simpa only [forcedScalarFlow, if_neg hz, if_neg hv0, if_pos hv1, middleFlow] using
      hasDerivAt_middleFlow hap ht ⟨le_of_not_ge hv0, hv1⟩
  · simpa only [forcedScalarFlow_eq_upperFlow hap (lt_of_not_ge hv1)] using
      hasDerivAt_upperFlow hap ht (lt_of_not_ge hv1)

end Eden.StrangeProof.Direct
