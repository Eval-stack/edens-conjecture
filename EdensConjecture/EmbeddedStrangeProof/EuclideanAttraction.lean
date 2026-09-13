import EdensConjecture.EmbeddedStrangeProof.Flow
import EdensConjecture.EmbeddedStrangeProof.PlanarAttraction

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

def radialLift (u : Eden.PhaseSpace 4) (t : ℝ) (q : ℝ × ℝ) : Eden.PhaseSpace 4 :=
  pack (((2 + q.1) / ‖fstC u‖ : ℝ) • (Complex.exp ((t : ℂ) * Complex.I) * fstC u))
    (((2 + q.2) / ‖sndC u‖ : ℝ) • (Complex.exp (((Real.sqrt 2 * t : ℝ) : ℂ) * Complex.I) * sndC u))

theorem radialLift_mem_attractor {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain)
    (t : ℝ) {q : ℝ × ℝ} (hq : q ∈ comb cantorSet gapFunction) : radialLift u t q ∈ directAttractor := by
  have hw1 : fstC u ≠ 0 := by intro h; have hh := hu.1; norm_num [h] at hh
  have hw2 : sndC u ≠ 0 := by intro h; have hh := hu.2.2.1; norm_num [h] at hh
  obtain ⟨hx, hy⟩ := directComb_bounds hq
  have h1 := norm_radial_rotation (r := 2 + q.1) (by linarith [hx.1]) hw1 t
  have h2 := norm_radial_rotation (r := 2 + q.2) (by linarith [hy.1]) hw2 (Real.sqrt 2 * t)
  change radialCoordinates (radialLift u t q) ∈ comb cantorSet gapFunction
  simpa only [radialCoordinates, radialLift, fstC_pack, sndC_pack, h1, h2, add_sub_cancel_left,
    Prod.mk.eta] using hq

theorem radial_rotation_difference (r s θ : ℝ) {w : ℂ} (hw : w ≠ 0) :
    ‖(r / ‖w‖ : ℝ) • (Complex.exp ((θ : ℂ) * Complex.I) * w) -
      (s / ‖w‖ : ℝ) • (Complex.exp ((θ : ℂ) * Complex.I) * w)‖ = |r - s| := by
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, ← sub_div, abs_div,
    abs_of_nonneg (norm_nonneg _), norm_mul, norm_exp_mul_I, one_mul,
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hw)]

theorem dist_directFlow_radialLift {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain)
    (t : ℝ) (q : ℝ × ℝ) :
    dist (directFlow t u) (radialLift u t q) ≤
      |scalarFlow t (‖fstC u‖ - 2) - q.1| +
        |forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) t (‖sndC u‖ - 2) - q.2| := by
  have hw1 : fstC u ≠ 0 := by intro h; have hh := hu.1; norm_num [h] at hh
  have hw2 : sndC u ≠ 0 := by intro h; have hh := hu.2.2.1; norm_num [h] at hh
  rw [dist_eq_norm]
  simp only [directFlow, combFlow, radialLift,
    show 2 + (‖fstC u‖ - 2) = ‖fstC u‖ by ring,
    show 2 + (‖sndC u‖ - 2) = ‖sndC u‖ by ring, pack_sub]
  have h := norm_pack_le
    (((2 + scalarFlow t (‖fstC u‖ - 2)) / ‖fstC u‖ : ℝ) • (Complex.exp ((t : ℂ) * Complex.I) * fstC u) -
      ((2 + q.1) / ‖fstC u‖ : ℝ) • (Complex.exp ((t : ℂ) * Complex.I) * fstC u))
    (((2 + forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) t (‖sndC u‖ - 2)) / ‖sndC u‖ : ℝ) •
      (Complex.exp (((Real.sqrt 2 * t : ℝ) : ℂ) * Complex.I) * sndC u) -
      ((2 + q.2) / ‖sndC u‖ : ℝ) • (Complex.exp (((Real.sqrt 2 * t : ℝ) : ℂ) * Complex.I) * sndC u))
  rw [radial_rotation_difference _ _ _ hw1, radial_rotation_difference _ _ _ hw2] at h
  simpa only [add_sub_add_left_eq_sub] using h

theorem directFlow_uniform_attraction :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      ∀ u ∈ phaseDomain, ∃ v ∈ directAttractor, dist (directFlow t u) v < ε := by
  intro ε hε
  let δ := min 1 (ε / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  refine ⟨attractionTime δ, (attractionTime_pos hδ).le, ?_⟩
  intro t ht u hu
  obtain ⟨hx, hy⟩ := phaseDomain_radial_mem hu
  obtain ⟨q, hq, h1, h2⟩ := planar_uniform_attraction hδ hδ1 ht hx hy
  refine ⟨radialLift u t q, radialLift_mem_attractor hu t hq, ?_⟩
  have h := dist_directFlow_radialLift hu t q
  linarith

end Eden.StrangeProof.Direct
