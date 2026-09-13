import EdensConjecture.EmbeddedStrangeProof.ForcedContinuity
import EdensConjecture.EmbeddedStrangeProof.Flow

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

theorem continuousOn_forcedScalarFlow_comp {α : Type*} [TopologicalSpace α]
    {S : Set α} {t a v : α → ℝ} (ht : ContinuousOn t S) (ha : ContinuousOn a S)
    (hv : ContinuousOn v S)
    (hmem : ∀ p ∈ S, 0 ≤ t p ∧ a p ∈ Icc 0 (1 / 2) ∧ v p ∈ Icc (-1) 2) :
    ContinuousOn (fun p => forcedScalarFlow (a p) (t p) (v p)) S := by
  exact (continuousOn_augmentedFlow.comp (ht.prodMk (ha.prodMk hv)) hmem).snd

theorem continuousOn_directFlow :
    ContinuousOn (fun p : ℝ × Eden.PhaseSpace 4 => directFlow p.1 p.2)
      (Ici 0 ×ˢ phaseDomain) := by
  let S : Set (ℝ × Eden.PhaseSpace 4) := Ici 0 ×ˢ phaseDomain
  have hn1 : Continuous (fun p : ℝ × Eden.PhaseSpace 4 => ‖fstC p.2‖) :=
    (continuous_fstC.comp continuous_snd).norm
  have hn2 : Continuous (fun p : ℝ × Eden.PhaseSpace 4 => ‖sndC p.2‖) :=
    (continuous_sndC.comp continuous_snd).norm
  have hx := hn1.sub (continuous_const (y := (2 : ℝ)))
  have hy := hn2.sub (continuous_const (y := (2 : ℝ)))
  have hg : Continuous (fun p : ℝ × Eden.PhaseSpace 4 => gapFunction (‖fstC p.2‖ - 2)) :=
    contDiff_gapFunction.continuous.comp hx
  have hr1 : ContinuousOn (fun p : ℝ × Eden.PhaseSpace 4 => scalarFlow p.1 (‖fstC p.2‖ - 2)) S := by
    have h := continuousOn_forcedScalarFlow_comp (S := S) continuous_fst.continuousOn
      (continuous_const (y := (0 : ℝ))).continuousOn hx.continuousOn (by
        intro p hp
        have hh := (phaseDomain_radial_mem hp.2).1
        exact ⟨hp.1, ⟨le_rfl, by norm_num⟩, hh.1.le, hh.2.le⟩)
    simpa [forcedScalarFlow] using h
  have hr2 : ContinuousOn (fun p : ℝ × Eden.PhaseSpace 4 =>
      forcedScalarFlow (gapFunction (‖fstC p.2‖ - 2)) p.1 (‖sndC p.2‖ - 2)) S := by
    apply continuousOn_forcedScalarFlow_comp continuous_fst.continuousOn hg.continuousOn hy.continuousOn
    intro p hp
    have hh := (phaseDomain_radial_mem hp.2).2
    exact ⟨hp.1, ⟨gapFunction_nonneg _, by linarith [gapFunction_le (‖fstC p.2‖ - 2)]⟩,
      hh.1.le, hh.2.le⟩
  have hs1 := ((continuousOn_const (c := (2 : ℝ))).add hr1).div hn1.continuousOn (by
    intro p hp
    exact ne_of_gt (lt_trans (by norm_num) hp.2.1))
  have hs2 := ((continuousOn_const (c := (2 : ℝ))).add hr2).div hn2.continuousOn (by
    intro p hp
    exact ne_of_gt (lt_trans (by norm_num) hp.2.2.2.1))
  have hp1 : ContinuousOn (fun p : ℝ × Eden.PhaseSpace 4 =>
      ((2 + scalarFlow p.1 (‖fstC p.2‖ - 2)) / ‖fstC p.2‖ : ℝ) •
        (Complex.exp ((p.1 : ℂ) * Complex.I) * fstC p.2)) S := by
    apply hs1.smul
    exact ((by fun_prop : Continuous (fun p : ℝ × Eden.PhaseSpace 4 =>
      Complex.exp ((p.1 : ℂ) * Complex.I))).mul
        (continuous_fstC.comp continuous_snd)).continuousOn
  have hp2 : ContinuousOn (fun p : ℝ × Eden.PhaseSpace 4 =>
      ((2 + forcedScalarFlow (gapFunction (‖fstC p.2‖ - 2)) p.1 (‖sndC p.2‖ - 2)) / ‖sndC p.2‖ : ℝ) •
        (Complex.exp (((Real.sqrt 2 * p.1 : ℝ) : ℂ) * Complex.I) * sndC p.2)) S := by
    apply hs2.smul
    exact ((by fun_prop : Continuous (fun p : ℝ × Eden.PhaseSpace 4 =>
      Complex.exp (((Real.sqrt 2 * p.1 : ℝ) : ℂ) * Complex.I))).mul
        (continuous_sndC.comp continuous_snd)).continuousOn
  have h := contDiff_pack.continuous.comp_continuousOn (hp1.prodMk hp2)
  convert! h using 1
  funext p
  simp only [directFlow, combFlow, Function.comp_apply,
    show 2 + (‖fstC p.2‖ - 2) = ‖fstC p.2‖ by ring,
    show 2 + (‖sndC p.2‖ - 2) = ‖sndC p.2‖ by ring]

end Eden.StrangeProof.Direct
