import EdensConjecture.EmbeddedStrangeProof.ForcedContinuity
import EdensConjecture.EmbeddedStrangeProof.ScalarRegularity
import EdensConjecture.EmbeddedStrangeProof.Gap
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof
open Set Filter
open scoped Topology

theorem hasFDerivAt_of_flat_error {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F H g : E → ℝ} {x : E} {L : E →L[ℝ] ℝ} {C : ℝ}
    (hH : HasFDerivAt H L x) (hg : HasFDerivAt g (0 : E →L[ℝ] ℝ) x) (hgz : g x = 0)
    (he : F x = H x) (hb : ∀ᶠ y in 𝓝 x, ‖F y - H y‖ ≤ C * ‖g y‖) :
    HasFDerivAt F L x := by
  have hsmall : g =o[𝓝 x] (fun y => y - x) := by
    simpa [hgz] using hg.isLittleO
  have herr : HasFDerivAt (fun y => F y - H y) (0 : E →L[ℝ] ℝ) x := by
    apply HasFDerivAt.of_isLittleO
    simpa [he] using (Asymptotics.IsBigO.of_bound C hb).trans_isLittleO hsmall
  have hh := hH.add herr
  simp only [add_zero] at hh
  convert! hh using 1
  funext y
  simp

namespace Direct

theorem hasDerivAt_gapFunction_zero {x : ℝ} (hx : gapFunction x = 0) :
    HasDerivAt gapFunction 0 x := by
  have hm : IsLocalMin gapFunction x := Filter.Eventually.of_forall (fun y => by
    rw [hx]
    exact gapFunction_nonneg y)
  have hd := hasDerivAt_gapFunction x
  rw [hm.hasDerivAt_eq_zero hd] at hd
  exact hd

theorem forcedScalarFlow_parameter_bound {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ x : ℝ, ∀ y ∈ Icc (-1 : ℝ) 2,
      ‖forcedScalarFlow (gapFunction x) t y - scalarFlow t y‖ ≤ C * ‖gapFunction x‖ := by
  obtain ⟨K, hK⟩ := exists_augmentedFlow_dist_bound
  refine ⟨Real.exp (K * t), ?_⟩
  intro x y hy
  have hp : (gapFunction x, y) ∈ scalarPhaseBox :=
    ⟨⟨gapFunction_nonneg x, (gapFunction_le x).trans (by norm_num)⟩, hy⟩
  have hq : ((0 : ℝ), y) ∈ scalarPhaseBox := ⟨⟨le_rfl, by norm_num⟩, hy⟩
  have hb := hK _ hp _ hq t ht
  have hs : dist (forcedScalarFlow (gapFunction x) t y) (forcedScalarFlow 0 t y) ≤
      dist (augmentedFlow t (gapFunction x, y)) (augmentedFlow t (0, y)) :=
    le_max_right _ _
  have h := hs.trans hb
  simpa [forcedScalarFlow, dist_prod_same_right, dist_eq_norm, mul_comm] using h

theorem hasFDerivAt_forcedScalarFlow_zero_parameter {t : ℝ} (ht : 0 ≤ t)
    {p : ℝ × ℝ} (hg : gapFunction p.1 = 0) (hl : -1 < p.2) (hu : p.2 < 2) :
    HasFDerivAt (fun q : ℝ × ℝ => forcedScalarFlow (gapFunction q.1) t q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => scalarFlow t q.2) p) p := by
  obtain ⟨C, hC⟩ := forcedScalarFlow_parameter_bound ht
  have hH : HasFDerivAt (fun q : ℝ × ℝ => scalarFlow t q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => scalarFlow t q.2) p) p :=
    ((contDiff_scalarFlow ht).comp contDiff_snd).differentiable (by norm_num) p |>.hasFDerivAt
  have hgap : HasFDerivAt (fun q : ℝ × ℝ => gapFunction q.1) (0 : (ℝ × ℝ) →L[ℝ] ℝ) p := by
    convert! (hasDerivAt_gapFunction_zero hg).comp_hasFDerivAt p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p)) using 1 <;> simp
  apply hasFDerivAt_of_flat_error hH hgap hg
    (by simp [forcedScalarFlow, hg])
  filter_upwards [continuous_snd.continuousAt.eventually (Ioo_mem_nhds hl hu)] with q hq
  exact hC q.1 q.2 ⟨hq.1.le, hq.2.le⟩

end Direct
end Eden.StrangeProof
