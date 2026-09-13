import EdensConjecture.EmbeddedStrangeProof.FlowContinuity
import EdensConjecture.EmbeddedStrangeProof.EuclideanODE
import EdensConjecture.EmbeddedStrangeProof.DerivativeCriterion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

theorem directFlow_local_inverse_bound {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 u, dist v u ≤ C * dist (directFlow t v) (directFlow t u) := by
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (isOpen_phaseDomain.mem_nhds hu)
  let B := Metric.closedBall u r
  let T := (fun p : ℝ × Eden.PhaseSpace 4 => directFlow p.1 p.2) '' (Icc 0 t ×ˢ B)
  have hB : B ⊆ phaseDomain := hball
  have hprod : Icc 0 t ×ˢ B ⊆ Ici 0 ×ˢ phaseDomain :=
    fun p hp => ⟨hp.1.1, hB hp.2⟩
  have hT : IsCompact T :=
    (isCompact_Icc.prod (isCompact_closedBall u r)).image_of_continuousOn
      (continuousOn_directFlow.mono hprod)
  have hTU : T ⊆ phaseDomain := by
    rintro z ⟨p, hp, rfl⟩
    exact directFlow_forward_invariant hp.1.1 (hB hp.2)
  have hlocal : LocallyLipschitzOn T (fun z => -directField z) := by
    intro z hz
    have hd := ((contDiffOn_directField z (hTU hz)).contDiffAt
      (isOpen_phaseDomain.mem_nhds (hTU hz))).neg
    obtain ⟨K, V, hV, hK⟩ := hd.exists_lipschitzOnWith
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩
  obtain ⟨K, hK⟩ := hlocal.exists_lipschitzOnWith_of_compact hT
  refine ⟨Real.exp (K * t), ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds u hr] with v hv
  have huB : u ∈ B := Metric.mem_closedBall_self hr.le
  have hd {z : Eden.PhaseSpace 4} (hz : z ∈ B) {s : ℝ} (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun s => directFlow (t - s) z) (-directField (directFlow (t - s) z)) s := by
    have hh := (hasDerivAt_directFlow (hB hz) (sub_nonneg.mpr hs.2)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    convert! hh using 1 <;> simp
  have hmem {z : Eden.PhaseSpace 4} (hz : z ∈ B) {s : ℝ} (hs : s ∈ Icc 0 t) :
      directFlow (t - s) z ∈ T := by
    exact ⟨(t - s, z), ⟨⟨sub_nonneg.mpr hs.2, by linarith [hs.1]⟩, hz⟩, rfl⟩
  have hh := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ z => -directField z) (s := fun _ => T) (a := 0) (b := t)
    (fun _ _ => hK)
    (fun s hs => (hd hv hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd hv ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => hmem hv ⟨hs.1, hs.2.le⟩)
    (fun s hs => (hd huB hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd huB ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (fun s hs => hmem huB ⟨hs.1, hs.2.le⟩)
    (δ := dist (directFlow t v) (directFlow t u)) (by simp)
    t ⟨ht, le_rfl⟩
  simpa [directFlow_zero (hB hv), directFlow_zero hu, mul_comm] using hh

/-- The injectivity obligation follows from differentiability, independently of
the explicit Jacobian formula. No differentiability assumption is discharged here. -/
theorem directFlow_derivative_injective_of_differentiable
    {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain) {t : ℝ} (ht : 0 ≤ t)
    (hd : DifferentiableAt ℝ (directFlow t) u) :
    Function.Injective (fderiv ℝ (directFlow t) u) := by
  obtain ⟨C, hC⟩ := directFlow_local_inverse_bound hu ht
  exact Eden.StrangeProof.derivative_injective_of_inverse_bound hd.hasFDerivAt hC

theorem directFlow_derivative_injective_of_contDiffOn {t : ℝ} (ht : 0 ≤ t)
    (hreg : ContDiffOn ℝ 1 (directFlow t) phaseDomain) :
    ∀ u ∈ phaseDomain, Function.Injective (fderiv ℝ (directFlow t) u) := by
  intro u hu
  exact directFlow_derivative_injective_of_differentiable hu ht
    (((hreg u hu).contDiffAt (isOpen_phaseDomain.mem_nhds hu)).differentiableAt (by norm_num))

end Eden.StrangeProof.Direct
