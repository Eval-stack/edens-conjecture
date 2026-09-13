import EdensConjecture.EmbeddedStrangeProof.Geometry
import EdensConjecture.EmbeddedStrangeProof.ForcedBounds

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

theorem phaseDomain_radial_mem {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain) :
    ‖fstC u‖ - 2 ∈ Ioo (-1 : ℝ) 2 ∧ ‖sndC u‖ - 2 ∈ Ioo (-1 : ℝ) 2 := by
  rcases hu with ⟨h1, h2, h3, h4⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

theorem norm_radial_rotation {r : ℝ} (hr : 0 ≤ r) {w : ℂ} (hw : w ≠ 0) (θ : ℝ) :
    ‖(r / ‖w‖ : ℝ) • (Complex.exp ((θ : ℂ) * Complex.I) * w)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr (norm_nonneg _)),
    norm_mul, norm_exp_mul_I, one_mul, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hw)]

theorem directFlow_norms {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖fstC (directFlow t u)‖ = 2 + scalarFlow t (‖fstC u‖ - 2) ∧
      ‖sndC (directFlow t u)‖ = 2 + forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) t (‖sndC u‖ - 2) := by
  obtain ⟨hx, hy⟩ := phaseDomain_radial_mem hu
  have hx' := scalarFlow_mem_domain ht hx
  have hy' := forcedScalarFlow_mem_domain (gapFunction_nonneg _) (by linarith [gapFunction_le (‖fstC u‖ - 2)]) ht hy
  have hw1 : fstC u ≠ 0 := by intro h; have hh := hu.1; norm_num [h] at hh
  have hw2 : sndC u ≠ 0 := by intro h; have hh := hu.2.2.1; norm_num [h] at hh
  simp only [directFlow, combFlow, fstC_pack, sndC_pack,
    show 2 + (‖fstC u‖ - 2) = ‖fstC u‖ by ring,
    show 2 + (‖sndC u‖ - 2) = ‖sndC u‖ by ring]
  exact ⟨norm_radial_rotation (by linarith [hx'.1]) hw1 t,
    norm_radial_rotation (by linarith [hy'.1]) hw2 (Real.sqrt 2 * t)⟩

theorem directFlow_forward_invariant {t : ℝ} (ht : 0 ≤ t) : MapsTo (directFlow t) phaseDomain phaseDomain := by
  intro u hu
  obtain ⟨hx, hy⟩ := phaseDomain_radial_mem hu
  have hx' := scalarFlow_mem_domain ht hx
  have hy' := forcedScalarFlow_mem_domain (gapFunction_nonneg _) (by linarith [gapFunction_le (‖fstC u‖ - 2)]) ht hy
  obtain ⟨h1, h2⟩ := directFlow_norms hu ht
  change 1 < ‖fstC (directFlow t u)‖ ∧ ‖fstC (directFlow t u)‖ < 4 ∧
    1 < ‖sndC (directFlow t u)‖ ∧ ‖sndC (directFlow t u)‖ < 4
  rw [h1, h2]
  exact ⟨by linarith [hx'.1], by linarith [hx'.2], by linarith [hy'.1], by linarith [hy'.2]⟩

end Eden.StrangeProof.Direct
