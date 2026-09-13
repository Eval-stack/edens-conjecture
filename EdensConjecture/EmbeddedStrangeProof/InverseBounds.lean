import EdensConjecture.EmbeddedStrangeProof.ForcedContinuity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set
open scoped NNReal

/-- Backward stability on a finite forward trajectory. This estimate does not
assume that a globally defined backward flow exists. -/
theorem exists_augmentedFlow_inverse_dist_bound : ∃ K : ℝ≥0,
    ∀ p ∈ scalarPhaseBox, ∀ q ∈ scalarPhaseBox, ∀ t ≥ 0,
      dist p q ≤ dist (augmentedFlow t p) (augmentedFlow t q) * Real.exp (K * t) := by
  obtain ⟨K, hK⟩ := contDiff_augmentedField.neg.contDiffOn.exists_lipschitzOnWith
    (by norm_num) ((convex_Icc (0 : ℝ) (1 / 2)).prod (convex_Icc (-1 : ℝ) 2))
    (isCompact_Icc.prod isCompact_Icc)
  refine ⟨K, ?_⟩
  intro p hp q hq t ht
  have hd {z : ℝ × ℝ} (hz : z ∈ scalarPhaseBox) {s : ℝ} (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun s => augmentedFlow (t - s) z)
        (-augmentedField (augmentedFlow (t - s) z)) s := by
    have hh := (hasDerivAt_augmentedFlow hz.1.1 (sub_nonneg.mpr hs.2)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    convert! hh using 1 <;> simp
  have h := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ z => -augmentedField z) (s := fun _ => scalarPhaseBox) (a := 0) (b := t)
    (fun _ _ => hK)
    (fun s hs => (hd hp hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd hp ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => augmentedFlow_mem hp (sub_nonneg.mpr hs.2.le))
    (fun s hs => (hd hq hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd hq ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => augmentedFlow_mem hq (sub_nonneg.mpr hs.2.le))
    (δ := dist (augmentedFlow t p) (augmentedFlow t q)) (by simp)
    t ⟨ht, le_rfl⟩
  simpa [augmentedFlow_zero hp.1.1, augmentedFlow_zero hq.1.1] using h

theorem augmentedFlow_injOn {t : ℝ} (ht : 0 ≤ t) :
    InjOn (augmentedFlow t) scalarPhaseBox := by
  obtain ⟨K, hK⟩ := exists_augmentedFlow_inverse_dist_bound
  intro p hp q hq heq
  have h := hK p hp q hq t ht
  rw [heq, dist_self, zero_mul] at h
  exact dist_le_zero.mp h

end Eden.StrangeProof.Direct
