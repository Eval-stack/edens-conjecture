import EdensConjecture.EmbeddedStrangeProof.GapFlowRegularity
import EdensConjecture.EmbeddedStrangeProof.FlowInverse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

theorem contDiffOn_directFlow {t : ℝ} (ht : 0 ≤ t) :
    ContDiffOn ℝ 1 (directFlow t) phaseDomain := by
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
  have hn1 : ContDiffAt ℝ 1 (fun v => ‖fstC v‖) u := (contDiffAt_norm ℝ hz).comp u hf
  have hn2 : ContDiffAt ℝ 1 (fun v => ‖sndC v‖) u := (contDiffAt_norm ℝ hw).comp u hs
  have hx : ContDiffAt ℝ 1 (fun v => scalarFlow t (‖fstC v‖ - 2)) u :=
    (contDiff_scalarFlow ht).contDiffAt.comp u (hn1.sub contDiffAt_const)
  have hcoords : ContDiffAt ℝ 1 radialCoordinates u :=
    (hn1.sub contDiffAt_const).prodMk (hn2.sub contDiffAt_const)
  have hmem : radialCoordinates u ∈ scalarStrip := (phaseDomain_radial_mem hu).2
  have hy : ContDiffAt ℝ 1
      (fun v => forcedScalarFlow (gapFunction (‖fstC v‖ - 2)) t (‖sndC v‖ - 2)) u := by
    exact ((contDiffOn_gapFlow ht).contDiffAt (isOpen_scalarStrip.mem_nhds hmem)).snd.comp u hcoords
  have hr1 := ((contDiffAt_const (c := (2 : ℝ))).add hx).div (contDiffAt_const.add (hn1.sub contDiffAt_const))
    (show 2 + (‖fstC u‖ - 2) ≠ 0 by simpa using norm_ne_zero_iff.mpr hz)
  have hr2 := ((contDiffAt_const (c := (2 : ℝ))).add hy).div (contDiffAt_const.add (hn2.sub contDiffAt_const))
    (show 2 + (‖sndC u‖ - 2) ≠ 0 by simpa using norm_ne_zero_iff.mpr hw)
  have hp : ContDiffAt ℝ 1 (fun v =>
      (((2 + scalarFlow t (‖fstC v‖ - 2)) / (2 + (‖fstC v‖ - 2)) : ℝ) •
        (Complex.exp ((t : ℂ) * Complex.I) * fstC v),
       ((2 + forcedScalarFlow (gapFunction (‖fstC v‖ - 2)) t (‖sndC v‖ - 2)) /
          (2 + (‖sndC v‖ - 2)) : ℝ) •
        (Complex.exp (((Real.sqrt 2 * t : ℝ) : ℂ) * Complex.I) * sndC v))) u :=
    (hr1.smul (contDiffAt_const.mul hf)).prodMk (hr2.smul (contDiffAt_const.mul hs))
  have hpack : ContDiff ℝ 1 (fun p : ℂ × ℂ => pack p.1 p.2) := contDiff_pack.of_le (by simp)
  exact (hpack.contDiffAt.comp u hp).contDiffWithinAt

theorem directFlow_derivative_injective {t : ℝ} (ht : 0 ≤ t) :
    ∀ u ∈ phaseDomain, Function.Injective (fderiv ℝ (directFlow t) u) :=
  directFlow_derivative_injective_of_contDiffOn ht (contDiffOn_directFlow ht)

end Eden.StrangeProof.Direct
