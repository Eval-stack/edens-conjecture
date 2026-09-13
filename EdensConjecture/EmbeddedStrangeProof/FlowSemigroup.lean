import EdensConjecture.EmbeddedStrangeProof.ForcedSemigroup
import EdensConjecture.EmbeddedStrangeProof.Flow

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

theorem radial_rotation_comp {r q : ℝ} (hq : q ≠ 0) {w : ℂ}
    (hw : w ≠ 0) (θ η : ℝ) :
    (r / q : ℝ) • (Complex.exp ((θ : ℂ) * Complex.I) *
      ((q / ‖w‖ : ℝ) • (Complex.exp ((η : ℂ) * Complex.I) * w))) =
    (r / ‖w‖ : ℝ) • (Complex.exp (((θ + η : ℝ) : ℂ) * Complex.I) * w) := by
  rw [mul_smul_comm, smul_smul]
  have hr : r / q * (q / ‖w‖) = r / ‖w‖ := by field_simp
  rw [hr, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem directFlow_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain) :
    directFlow (t + s) u = directFlow t (directFlow s u) := by
  obtain ⟨hn1, hn2⟩ := directFlow_norms hu hs
  have hx : ‖fstC (directFlow s u)‖ - 2 = scalarFlow s (‖fstC u‖ - 2) := by rw [hn1]; ring
  have hy : ‖sndC (directFlow s u)‖ - 2 =
      forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) s (‖sndC u‖ - 2) := by rw [hn2]; ring
  have hg : gapFunction (‖fstC (directFlow s u)‖ - 2) = gapFunction (‖fstC u‖ - 2) := by
    rw [hx, gapFunction_scalarFlow hs]
  have hsu := directFlow_forward_invariant hs hu
  have hw1 : fstC u ≠ 0 := by intro h; have hh := hu.1; norm_num [h] at hh
  have hw2 : sndC u ≠ 0 := by intro h; have hh := hu.2.2.1; norm_num [h] at hh
  have hq1 : 2 + scalarFlow s (‖fstC u‖ - 2) ≠ 0 := by
    rw [← hn1]; exact ne_of_gt (lt_trans (by norm_num) hsu.1)
  have hq2 : 2 + forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) s (‖sndC u‖ - 2) ≠ 0 := by
    rw [← hn2]; exact ne_of_gt (lt_trans (by norm_num) hsu.2.2.1)
  have hform (q : ℝ) (p : Eden.PhaseSpace 4) : directFlow q p =
      pack (((2 + scalarFlow q (‖fstC p‖ - 2)) / ‖fstC p‖ : ℝ) •
        (Complex.exp ((q : ℂ) * Complex.I) * fstC p))
      (((2 + forcedScalarFlow (gapFunction (‖fstC p‖ - 2)) q (‖sndC p‖ - 2)) / ‖sndC p‖ : ℝ) •
        (Complex.exp (((Real.sqrt 2 * q : ℝ) : ℂ) * Complex.I) * sndC p)) := by
    simp only [directFlow, combFlow, show 2 + (‖fstC p‖ - 2) = ‖fstC p‖ by ring,
      show 2 + (‖sndC p‖ - 2) = ‖sndC p‖ by ring]
  rw [hform (t + s) u, hform t (directFlow s u), hg, hx, hy, hn1, hn2]
  rw [hform s u]
  simp only [fstC_pack, sndC_pack]
  rw [scalarFlow_semigroup ht hs, forcedScalarFlow_semigroup (gapFunction_nonneg _) ht hs,
    radial_rotation_comp hq1 hw1, radial_rotation_comp hq2 hw2]
  congr 3
  rw [mul_add]

end Eden.StrangeProof.Direct
