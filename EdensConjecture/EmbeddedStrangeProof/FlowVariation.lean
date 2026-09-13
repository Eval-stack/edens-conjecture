import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic

noncomputable section
namespace Eden.StrangeProof
open Set Filter
open scoped Topology NNReal

theorem flow_sub_initial_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {φ ψ : ℝ → E} {S : Set E} {K : ℝ≥0} {t : ℝ}
    (ht : 0 ≤ t) (hK : LipschitzOnWith K F S)
    (hφ : ∀ s ∈ Icc 0 t, HasDerivAt φ (F (φ s)) s)
    (hψ : ∀ s ∈ Icc 0 t, HasDerivAt ψ (F (ψ s)) s)
    (hφS : ∀ s ∈ Icc 0 t, φ s ∈ S) (hψS : ∀ s ∈ Icc 0 t, ψ s ∈ S) :
    ‖(φ t - ψ t) - (φ 0 - ψ 0)‖ ≤
      (K * t * Real.exp (K * t)) * ‖φ 0 - ψ 0‖ := by
  have hb (s : ℝ) (hs : s ∈ Icc 0 t) :
      dist (φ s) (ψ s) ≤ dist (φ 0) (ψ 0) * Real.exp (K * s) := by
    have h := dist_le_of_trajectories_ODE_of_mem
      (v := fun _ => F) (s := fun _ => S) (a := 0) (b := t)
      (fun _ _ => hK)
      (fun r hr => (hφ r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hφ r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt)
      (fun r hr => hφS r ⟨hr.1, hr.2.le⟩)
      (fun r hr => (hψ r hr).continuousAt.continuousWithinAt)
      (fun r hr => (hψ r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt)
      (fun r hr => hψS r ⟨hr.1, hr.2.le⟩)
      (δ := dist (φ 0) (ψ 0)) le_rfl s hs
    simpa using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => φ s - ψ s) (f' := fun s => F (φ s) - F (ψ s))
    (a := 0) (b := t) (C := K * (dist (φ 0) (ψ 0) * Real.exp (K * t)))
    (fun s hs => ((hφ s hs).sub (hψ s hs)).hasDerivWithinAt)
    (by
      intro s hs
      have hs' : s ∈ Icc 0 t := ⟨hs.1, hs.2.le⟩
      calc
        ‖F (φ s) - F (ψ s)‖ ≤ K * dist (φ s) (ψ s) := by
          simpa [dist_eq_norm] using hK.dist_le_mul _ (hφS s hs') _ (hψS s hs')
        _ ≤ K * (dist (φ 0) (ψ 0) * Real.exp (K * t)) := by
          gcongr
          exact (hb s hs').trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs'.2 K.coe_nonneg)) (dist_nonneg)))
    t ⟨ht, le_rfl⟩
  convert! h using 1 <;> simp [dist_eq_norm] <;> ring

theorem continuousAt_fderiv_of_linear_error_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {L : E →L[ℝ] F} {x : E}
    (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hx : HasFDerivAt f L x)
    (hb : ∀ ε > 0, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ z ∈ U,
      ‖(f y - f z) - L (y - z)‖ ≤ ε * ‖y - z‖) :
    ContinuousAt (fderiv ℝ f) x := by
  rw [ContinuousAt, hx.fderiv]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U, hU, hbound⟩ := hb (ε / 2) (by positivity)
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
  filter_upwards [hVo.mem_nhds hxV, hd] with y hy hyd
  have hD := hyd.hasFDerivAt.sub L.hasFDerivAt
  have hnorm : ‖fderiv ℝ f y - L‖ ≤ ε / 2 := by
    apply hD.le_of_lip' (by positivity)
    filter_upwards [hVo.mem_nhds hy] with z hz
    have hh := hbound z (hVU hz) y (hVU hy)
    simpa only [map_sub, Pi.sub_apply, sub_sub_sub_comm] using hh
  rw [dist_eq_norm]
  linarith

theorem flow_eventually_mem_of_fixed {E : Type*} [NormedAddCommGroup E]
    {φ : ℝ → E → E} {U V : Set E} {x : E} {t : ℝ}
    (hU : IsOpen U) (hx : x ∈ U)
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc 0 t ×ˢ U))
    (hfix : ∀ s ∈ Icc 0 t, φ s x = x) (hV : V ∈ 𝓝 x) :
    ∃ W ∈ 𝓝 x, W ⊆ U ∧ ∀ s ∈ Icc 0 t, ∀ y ∈ W, φ s y ∈ V := by
  have hn := hc.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
    (t := {x}) (by simpa only [nhdsSet_singleton] using hV)
  have hsub : Icc 0 t ×ˢ ({x} : Set E) ⊆
      (Icc 0 t ×ˢ U) ∩ (fun p : ℝ × E => φ p.1 p.2) ⁻¹' {x} := by
    rintro ⟨s, y⟩ ⟨hs, rfl⟩
    exact ⟨⟨hs, hx⟩, hfix s hs⟩
  have hn' := (nhdsSetWithin_mono_left hsub) hn
  obtain ⟨W, hW, hb⟩ := generalized_tube_lemma_right isCompact_Icc isCompact_singleton hn'
  have hW' : W ∈ 𝓝 x := by
    simpa only [nhdsSetWithin_singleton, nhdsWithin_eq_nhds.mpr (hU.mem_nhds hx)] using hW
  refine ⟨W ∩ U, inter_mem hW' (hU.mem_nhds hx), inter_subset_right, ?_⟩
  intro s hs y hy
  exact hb (show (s, y) ∈ Icc 0 t ×ˢ W from ⟨hs, hy.1⟩)

theorem continuousAt_fderiv_flow_of_flat_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → E} {φ : ℝ → E → E} {U : Set E} {x : E} {t : ℝ}
    (ht : 0 ≤ t) (hU : IsOpen U) (hx : x ∈ U)
    (hF : ContDiffAt ℝ 1 F x) (hFzero : fderiv ℝ F x = 0)
    (hc : ContinuousOn (fun p : ℝ × E => φ p.1 p.2) (Icc 0 t ×ˢ U))
    (hfix : ∀ s ∈ Icc 0 t, φ s x = x)
    (hinit : ∀ y ∈ U, φ 0 y = y)
    (hODE : ∀ y ∈ U, ∀ s ∈ Icc 0 t, HasDerivAt (fun r => φ r y) (F (φ s y)) s)
    (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (φ t) y)
    (hdx : HasFDerivAt (φ t) (ContinuousLinearMap.id ℝ E) x) :
    ContinuousAt (fderiv ℝ (φ t)) x := by
  apply continuousAt_fderiv_of_linear_error_bound hd hdx
  intro ε hε
  have hcont : ContinuousAt (fun k : ℝ => k * t * Real.exp (k * t)) 0 := by fun_prop
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp hcont ε hε
  let k : ℝ := δ / 2
  have hk : 0 < k := by dsimp [k]; positivity
  have hkbound : k * t * Real.exp (k * t) < ε := by
    have h := hδb (show dist k 0 < δ by simp [Real.dist_eq, k, abs_of_pos hδ]; linarith)
    simpa [Real.dist_eq, abs_of_pos hk, abs_of_nonneg ht] using h
  have hs := hF.hasStrictFDerivAt (by norm_num)
  rw [hFzero] at hs
  obtain ⟨S, hS, hLip⟩ := hs.exists_lipschitzOnWith_of_nnnorm_lt ⟨k, hk.le⟩
    (by simpa only [nnnorm_zero] using (show (0 : ℝ≥0) < ⟨k, hk.le⟩ from hk))
  obtain ⟨W, hW, hWU, hmem⟩ := flow_eventually_mem_of_fixed hU hx hc hfix hS
  refine ⟨W, hW, ?_⟩
  intro y hy z hz
  have h := flow_sub_initial_bound ht hLip
    (hODE y (hWU hy)) (hODE z (hWU hz))
    (fun s hs => hmem s hs y hy) (fun s hs => hmem s hs z hz)
  simp only [hinit y (hWU hy), hinit z (hWU hz), NNReal.coe_mk] at h
  exact h.trans (mul_le_mul_of_nonneg_right hkbound.le (norm_nonneg _))

end Eden.StrangeProof
