import EdensConjecture.EmbeddedStrangeProof.TangentODE
import EdensConjecture.EmbeddedStrangeProof.Flow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

theorem hasDerivAt_radial_rotation {r : ℝ → ℝ} {d t : ℝ}
    (hr : HasDerivAt r d t) (hr0 : r t ≠ 0) (w : ℂ) (ω : ℝ) :
    HasDerivAt (fun s => (r s / ‖w‖ : ℝ) •
      (Complex.exp (((ω * s : ℝ) : ℂ) * Complex.I) * w))
      (((((d / r t : ℝ) : ℂ) + (ω : ℂ) * Complex.I)) *
        ((r t / ‖w‖ : ℝ) • (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * w))) t := by
  have hlin : HasDerivAt (fun s : ℝ => ((ω * s : ℝ) : ℂ)) (ω : ℂ) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul ω).ofReal_comp
  have hphase := (hlin.mul_const Complex.I).cexp
  have hscale := (hr.div_const ‖w‖).ofReal_comp
  have hraw := (hscale.mul hphase).mul_const w
  convert! hraw using 1
  · ext s
    simp [Complex.real_smul, mul_assoc]
  · simp only [Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr0]
    <;> ring

theorem hasDerivAt_pack {f g : ℝ → ℂ} {f' g' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => pack (f s) (g s)) (pack f' g') t := by
  have hp : HasDerivAt (fun s => ![(f s).re, (f s).im, (g s).re, (g s).im])
      ![f'.re, f'.im, g'.re, g'.im] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
    · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
    · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
    · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hg
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hp

theorem hasDerivAt_directFlow {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => directFlow s u) (directField (directFlow t u)) t := by
  obtain ⟨h1, h2⟩ := directFlow_norms hu ht
  have hut := directFlow_forward_invariant ht hu
  have hp1 : 2 + scalarFlow t (‖fstC u‖ - 2) ≠ 0 := by
    rw [← h1]; exact ne_of_gt (lt_trans (by norm_num) hut.1)
  have hp2 : 2 + forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) t (‖sndC u‖ - 2) ≠ 0 := by
    rw [← h2]; exact ne_of_gt (lt_trans (by norm_num) hut.2.2.1)
  have hd1 := (hasDerivAt_scalarFlow ht (‖fstC u‖ - 2)).const_add 2
  have hd2 := (hasDerivAt_forcedScalarFlow (gapFunction_nonneg (‖fstC u‖ - 2)) ht
    (v := ‖sndC u‖ - 2)).const_add 2
  have hf := hasDerivAt_pack
    (hasDerivAt_radial_rotation hd1 hp1 (fstC u) 1)
    (hasDerivAt_radial_rotation hd2 hp2 (sndC u) (Real.sqrt 2))
  have hx : ‖fstC (directFlow t u)‖ - 2 = scalarFlow t (‖fstC u‖ - 2) := by rw [h1]; ring
  have hy : ‖sndC (directFlow t u)‖ - 2 =
      forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) t (‖sndC u‖ - 2) := by rw [h2]; ring
  have hg : gapFunction (‖fstC (directFlow t u)‖ - 2) = gapFunction (‖fstC u‖ - 2) := by
    rw [hx, gapFunction_scalarFlow ht]
  convert! hf using 1
  · ext s
    simp only [directFlow, combFlow, one_mul,
      show 2 + (‖fstC u‖ - 2) = ‖fstC u‖ by ring,
      show 2 + (‖sndC u‖ - 2) = ‖sndC u‖ by ring]
  · simp only [directField, combField, hg, hx, hy, h1, h2]
    simp only [show ∀ x : ℝ, 2 + x - 2 = x by intro x; ring, gapFunction_scalarFlow ht]
    simp only [directFlow, combFlow, fstC_pack, sndC_pack, one_mul, Complex.ofReal_one,
      show 2 + (‖fstC u‖ - 2) = ‖fstC u‖ by ring,
      show 2 + (‖sndC u‖ - 2) = ‖sndC u‖ by ring]
    congr 4 <;> push_cast <;> ring

end Eden.StrangeProof.Direct
