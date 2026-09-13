import EdensConjecture.EmbeddedStrangeProof.Geometry
import EdensConjecture.EmbeddedStrangeProof.Dimension

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample
open scoped NNReal ENNReal

def teeth : Set (Eden.PhaseSpace 4) := radialCoordinates ⁻¹' (cantorSet ×ˢ Icc 0 1)

theorem teeth_subset_attractor : teeth ⊆ directAttractor := fun _ h => Or.inr h

def dimensionProbe (u : Eden.PhaseSpace 4) : Fin 4 → ℝ :=
  ![cantorBinaryMap (‖fstC u‖ - 2), ‖sndC u‖ - 2, (fstC u).re, (sndC u).re]

theorem complex_coordinate_dist_le (u v : Eden.PhaseSpace 4) :
    dist (fstC u) (fstC v) ≤ dist u v ∧ dist (sndC u) (sndC v) ≤ dist u v := by
  have h := norm_pack_sq (fstC u - fstC v) (sndC u - sndC v)
  rw [← pack_sub, pack_fstC_sndC, pack_fstC_sndC] at h
  simp only [dist_eq_norm]
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [sq_nonneg ‖sndC u - sndC v‖]
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    nlinarith [sq_nonneg ‖fstC u - fstC v‖]

theorem bounded_lipschitz_holder {z d : ℝ} (hd : 0 ≤ d) (hzd : z ≤ d) (hz6 : z ≤ 6) :
    z ≤ 7 * d ^ (4 / 5 : ℝ) := by
  by_cases hd1 : d ≤ 1
  · have h := Real.rpow_le_rpow_of_exponent_ge' hd hd1
      (by norm_num : (0 : ℝ) ≤ 4 / 5) (by norm_num : (4 / 5 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h
    have h0 := Real.rpow_nonneg hd (4 / 5 : ℝ)
    linarith
  · have h : 1 ≤ d ^ (4 / 5 : ℝ) := by
      simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
        (le_of_not_ge hd1) (by norm_num : (0 : ℝ) ≤ 4 / 5)
    linarith

theorem dimensionProbe_holder_bound {u v : Eden.PhaseSpace 4}
    (hu : u ∈ teeth) (hv : v ∈ teeth) :
    dist (dimensionProbe u) (dimensionProbe v) ≤ 7 * dist u v ^ (4 / 5 : ℝ) := by
  have hcoord := complex_coordinate_dist_le u v
  rw [dist_eq_norm (fstC u), dist_eq_norm (sndC u)] at hcoord
  have huB := directComb_bounds (teeth_subset_attractor hu)
  have hvB := directComb_bounds (teeth_subset_attractor hv)
  have hu1 : ‖fstC u‖ ≤ 3 := by have h := huB.1.2; change ‖fstC u‖ - 2 ≤ 1 at h; linarith
  have hv1 : ‖fstC v‖ ≤ 3 := by have h := hvB.1.2; change ‖fstC v‖ - 2 ≤ 1 at h; linarith
  have hu2 : ‖sndC u‖ ≤ 3 := by have h := huB.2.2; change ‖sndC u‖ - 2 ≤ 1 at h; linarith
  have hv2 : ‖sndC v‖ ≤ 3 := by have h := hvB.2.2; change ‖sndC v‖ - 2 ≤ 1 at h; linarith
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [dimensionProbe, Matrix.cons_val_zero, Real.dist_eq]
    have h := cantorBinaryMap_holder_bound hu.1 hv.1
    have hr : |(‖fstC u‖ - 2) - (‖fstC v‖ - 2)| ≤ dist u v := by
      simpa only [sub_sub_sub_cancel_right] using (abs_norm_sub_norm_le (fstC u) (fstC v)).trans hcoord.1
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hr (by norm_num)) (by norm_num))
  · change |(‖sndC u‖ - 2) - (‖sndC v‖ - 2)| ≤ _
    apply bounded_lipschitz_holder dist_nonneg
    · simpa only [sub_sub_sub_cancel_right] using (abs_norm_sub_norm_le (sndC u) (sndC v)).trans hcoord.2
    · have h1 := hu.2.1
      have h2 := hu.2.2
      have h3 := hv.2.1
      have h4 := hv.2.2
      change 0 ≤ ‖sndC u‖ - 2 at h1
      change ‖sndC u‖ - 2 ≤ 1 at h2
      change 0 ≤ ‖sndC v‖ - 2 at h3
      change ‖sndC v‖ - 2 ≤ 1 at h4
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |(fstC u).re - (fstC v).re| ≤ _
    apply bounded_lipschitz_holder dist_nonneg
    · exact (show |(fstC u).re - (fstC v).re| ≤ ‖fstC u - fstC v‖ by
        simpa only [Complex.sub_re] using Complex.abs_re_le_norm (fstC u - fstC v)).trans hcoord.1
    · have h : |(fstC u).re - (fstC v).re| ≤ |(fstC u).re| + |(fstC v).re| := by
        simpa using abs_sub_le (fstC u).re 0 (fstC v).re
      linarith [Complex.abs_re_le_norm (fstC u), Complex.abs_re_le_norm (fstC v)]
  · change |(sndC u).re - (sndC v).re| ≤ _
    apply bounded_lipschitz_holder dist_nonneg
    · exact (show |(sndC u).re - (sndC v).re| ≤ ‖sndC u - sndC v‖ by
        simpa only [Complex.sub_re] using Complex.abs_re_le_norm (sndC u - sndC v)).trans hcoord.2
    · have h : |(sndC u).re - (sndC v).re| ≤ |(sndC u).re| + |(sndC v).re| := by
        simpa using abs_sub_le (sndC u).re 0 (sndC v).re
      linarith [Complex.abs_re_le_norm (sndC u), Complex.abs_re_le_norm (sndC v)]

theorem holderOnWith_dimensionProbe : HolderOnWith 7 (4 / 5) dimensionProbe teeth := by
  intro u hu v hv
  have h := ENNReal.ofReal_le_ofReal (dimensionProbe_holder_bound hu hv)
  simpa only [edist_dist, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7),
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5),
    ENNReal.ofReal_ofNat, ENNReal.coe_ofNat, NNReal.coe_div, NNReal.coe_ofNat] using h

def complexOfRadius (r a : ℝ) : ℂ := (a : ℂ) + (Real.sqrt (r ^ 2 - a ^ 2) : ℂ) * Complex.I

theorem norm_complexOfRadius {r a : ℝ} (hr : 0 ≤ r) (ha : a ^ 2 ≤ r ^ 2) :
    ‖complexOfRadius r a‖ = r := by
  have hsq : ‖complexOfRadius r a‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm]
    simp only [complexOfRadius, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
      zero_mul, sub_self, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add]
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr ha)]
  nlinarith [norm_nonneg (complexOfRadius r a)]

theorem cube_subset_dimensionProbe_image :
    (Set.pi univ fun _ : Fin 4 => Icc (0 : ℝ) 1) ⊆ dimensionProbe '' teeth := by
  intro p hp
  have hp0 := hp 0 (mem_univ _)
  have hp1 := hp 1 (mem_univ _)
  have hp2 := hp 2 (mem_univ _)
  have hp3 := hp 3 (mem_univ _)
  obtain ⟨e, _, he⟩ := binaryCode_surjOn hp0
  have hx := cantorCode_mem e
  have hnorm1 : ‖complexOfRadius (2 + cantorCode e) (p 2)‖ = 2 + cantorCode e := by
    apply norm_complexOfRadius (by linarith [hx.1])
    nlinarith [hp2.1, hp2.2, hx.1, sq_nonneg (cantorCode e)]
  have hnorm2 : ‖complexOfRadius (2 + p 1) (p 3)‖ = 2 + p 1 := by
    apply norm_complexOfRadius (by linarith [hp1.1])
    nlinarith [hp3.1, hp3.2, hp1.1, sq_nonneg (p 1)]
  refine ⟨pack (complexOfRadius (2 + cantorCode e) (p 2)) (complexOfRadius (2 + p 1) (p 3)), ?_, ?_⟩
  · change (‖fstC _‖ - 2 ∈ cantorSet) ∧ (‖sndC _‖ - 2 ∈ Icc (0 : ℝ) 1)
    simpa only [fstC_pack, sndC_pack, hnorm1, hnorm2, add_sub_cancel_left, cantorSet] using
      And.intro (mem_range_self e : cantorCode e ∈ cantorSet) hp1
  · funext i
    fin_cases i <;> simp [dimensionProbe, hnorm1, hnorm2, cantorBinaryMap_code, he] <;>
      simp [complexOfRadius]

theorem dimH_four_cube : dimH (Set.pi univ fun _ : Fin 4 => Icc (0 : ℝ) 1) = 4 := by
  have h : (interior (Set.pi univ fun _ : Fin 4 => Icc (0 : ℝ) 1)).Nonempty := by
    rw [interior_pi_set finite_univ]
    refine ⟨fun _ => 1 / 2, ?_⟩
    intro i hi
    rw [interior_Icc]
    norm_num
  simpa using Real.dimH_of_nonempty_interior h

theorem directAttractor_dimH_lower : (16 : ENNReal) / 5 ≤ dimH directAttractor := by
  have h := (dimH_mono cube_subset_dimensionProbe_image).trans
    (holderOnWith_dimensionProbe.dimH_image_le (by norm_num : (0 : ℝ≥0) < 4 / 5))
  rw [dimH_four_cube] at h
  have hm := (ENNReal.le_div_iff_mul_le
    (Or.inl (by norm_num : ((4 / 5 : ℝ≥0) : ENNReal) ≠ 0))
    (Or.inl ENNReal.coe_ne_top)).mp h
  have ht := hm.trans (dimH_mono teeth_subset_attractor)
  norm_num at ht
  rw [← mul_div_assoc] at ht
  norm_num at ht
  exact ht

end Eden.StrangeProof.Direct
