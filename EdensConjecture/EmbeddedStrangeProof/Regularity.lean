import EdensConjecture.EmbeddedStrangeProof.Gap
import EdensConjecture.EmbeddedStrangeProof.Geometry

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

theorem hasDerivAt_positiveSquare (x : ℝ) :
    HasDerivAt (fun y : ℝ => max y 0 ^ 2) (2 * max x 0) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : (fun y : ℝ => max y 0 ^ 2) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [max_eq_right (le_of_lt (show y < 0 from hy))]
    simpa [max_eq_right hx.le] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  · have hb : (fun y : ℝ => max y 0 ^ 2) =O[𝓝 0] (fun y : ℝ => ‖y - 0‖ ^ 2) := by
      apply Asymptotics.IsBigO.of_bound'
      apply Eventually.of_forall
      intro y
      by_cases hy : y ≤ 0
      · simpa [max_eq_right hy] using sq_nonneg y
      · simp [max_eq_left (le_of_not_ge hy), Real.norm_eq_abs, sq_abs, abs_of_nonneg (sq_nonneg y)]
    have hs := hb.trans_isLittleO
      (Asymptotics.isLittleO_pow_sub_sub (0 : ℝ) (by decide : 1 < 2))
    rw [hasDerivAt_iff_isLittleO]
    simpa using hs
  · have heq : (fun y : ℝ => max y 0 ^ 2) =ᶠ[𝓝 x] (fun y => y ^ 2) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [max_eq_left (le_of_lt (show 0 < y from hy))]
    simpa [max_eq_left hx.le] using ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq heq

theorem contDiff_positiveSquare : ContDiff ℝ 1 (fun x : ℝ => max x 0 ^ 2) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_positiveSquare x).differentiableAt, ?_⟩
  have heq : deriv (fun x : ℝ => max x 0 ^ 2) = fun x => 2 * max x 0 :=
    funext fun x => (hasDerivAt_positiveSquare x).deriv
  rw [heq]
  fun_prop

theorem contDiff_restoring : ContDiff ℝ 1 restoring :=
  (contDiff_positiveSquare.comp (contDiff_id.sub contDiff_const)).sub
    (contDiff_positiveSquare.comp contDiff_id.neg)

open Eden.TorusCounterexample in
theorem contDiffOn_directField : ContDiffOn ℝ 1 directField phaseDomain := by
  intro u hu
  have hz : fstC u ≠ 0 := by
    intro h
    have := hu.1
    norm_num [h] at this
  have hw : sndC u ≠ 0 := by
    intro h
    have := hu.2.2.1
    norm_num [h] at this
  have hf : ContDiffAt ℝ 1 fstC u := (contDiff_fstC.of_le (by simp)).contDiffAt
  have hs : ContDiffAt ℝ 1 sndC u := (contDiff_sndC.of_le (by simp)).contDiffAt
  have hn1 : ContDiffAt ℝ 1 (fun v => ‖fstC v‖) u :=
    (contDiffAt_norm ℝ hz).comp u hf
  have hn2 : ContDiffAt ℝ 1 (fun v => ‖sndC v‖) u :=
    (contDiffAt_norm ℝ hw).comp u hs
  have hb1 : ContDiffAt ℝ 1 (fun v => restoring (‖fstC v‖ - 2)) u :=
    contDiff_restoring.contDiffAt.comp u (hn1.sub contDiffAt_const)
  have hb2 : ContDiffAt ℝ 1 (fun v => restoring (‖sndC v‖ - 2)) u :=
    contDiff_restoring.contDiffAt.comp u (hn2.sub contDiffAt_const)
  have hg : ContDiffAt ℝ 1 (fun v => gapFunction (‖fstC v‖ - 2)) u :=
    contDiff_gapFunction.contDiffAt.comp u (hn1.sub contDiffAt_const)
  have hr1 := hb1.neg.div hn1 (norm_ne_zero_iff.mpr hz)
  have hr2 := ((hg.pow 2).add hb2).neg.div hn2 (norm_ne_zero_iff.mpr hw)
  have hc1 := Complex.ofRealCLM.contDiff.contDiffAt.comp u hr1
  have hc2 := Complex.ofRealCLM.contDiff.contDiffAt.comp u hr2
  have hp : ContDiffAt ℝ 1 (fun v => (
      (((-restoring (‖fstC v‖ - 2) / ‖fstC v‖ : ℝ) : ℂ) + Complex.I) * fstC v,
      (((-(gapFunction (‖fstC v‖ - 2) ^ 2 + restoring (‖sndC v‖ - 2)) / ‖sndC v‖ : ℝ) : ℂ) +
        (Real.sqrt 2 : ℂ) * Complex.I) * sndC v)) u :=
    ((hc1.add contDiffAt_const).mul hf).prodMk
    ((hc2.add contDiffAt_const).mul hs)
  have hpack : ContDiff ℝ 1 (fun p : ℂ × ℂ => pack p.1 p.2) :=
    contDiff_pack.of_le (by simp)
  exact (hpack.contDiffAt.comp u hp).contDiffWithinAt

end Eden.StrangeProof.Direct
