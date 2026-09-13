import EdensConjecture.EmbeddedStrangeProof.Scalar
import EdensConjecture.EmbeddedStrangeProof.Gap
import EdensConjecture.MainProof.Torus

/-! Concrete geometry of the direct construction, including compactness,
invariance and aperiodicity of the proposed attractor. General flow laws and
attraction away from this set are separate obligations. -/

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

/-- Planar equilibrium comb: the lower graph together with the Cantor teeth. -/
def comb (C : Set ℝ) (gap : ℝ → ℝ) : Set (ℝ × ℝ) :=
  (fun x : ℝ => (x, -gap x)) '' Icc 0 1 ∪ C ×ˢ Icc 0 1

theorem isCompact_comb {C : Set ℝ} (hC : IsCompact C)
    {gap : ℝ → ℝ} (hg : Continuous gap) : IsCompact (comb C gap) := by
  exact (isCompact_Icc.image (continuous_id.prodMk hg.neg)).union
    (hC.prod isCompact_Icc)

theorem comb_nonempty (C : Set ℝ) (gap : ℝ → ℝ) : (comb C gap).Nonempty := by
  exact ⟨(0, -gap 0), Or.inl ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩

def phaseDomain : Set (Eden.PhaseSpace 4) :=
  {u | 1 < ‖fstC u‖ ∧ ‖fstC u‖ < 4 ∧ 1 < ‖sndC u‖ ∧ ‖sndC u‖ < 4}

def radialCoordinates (u : Eden.PhaseSpace 4) : ℝ × ℝ :=
  (‖fstC u‖ - 2, ‖sndC u‖ - 2)

def attractor (C : Set ℝ) (gap : ℝ → ℝ) : Set (Eden.PhaseSpace 4) :=
  radialCoordinates ⁻¹' comb C gap

/-- The vector field in equation (12), directly in Euclidean coordinates. -/
def combField (gap : ℝ → ℝ) (u : Eden.PhaseSpace 4) : Eden.PhaseSpace 4 :=
  let w₁ := fstC u
  let w₂ := sndC u
  pack (((( -restoring (‖w₁‖ - 2) / ‖w₁‖ : ℝ) : ℂ) + Complex.I) * w₁)
    ((((-(gap (‖w₁‖ - 2) ^ 2 + restoring (‖w₂‖ - 2)) / ‖w₂‖ : ℝ) : ℂ) +
      (Real.sqrt 2 : ℂ) * Complex.I) * w₂)

/-- The explicit time-map formula (19). Its C1-system obligations are not assumed. -/
def combFlow (gap : ℝ → ℝ) (t : ℝ) (u : Eden.PhaseSpace 4) : Eden.PhaseSpace 4 :=
  let w₁ := fstC u
  let w₂ := sndC u
  let x := ‖w₁‖ - 2
  let y := ‖w₂‖ - 2
  pack (((2 + scalarFlow t x) / (2 + x) : ℝ) •
      (Complex.exp ((t : ℂ) * Complex.I) * w₁))
    (((2 + forcedScalarFlow (gap x) t y) / (2 + y) : ℝ) •
      (Complex.exp (((Real.sqrt 2 * t : ℝ) : ℂ) * Complex.I) * w₂))

def directAttractor : Set (Eden.PhaseSpace 4) := attractor cantorSet gapFunction
def directField : Eden.PhaseSpace 4 → Eden.PhaseSpace 4 := combField gapFunction
def directFlow : ℝ → Eden.PhaseSpace 4 → Eden.PhaseSpace 4 := combFlow gapFunction

theorem continuous_radialCoordinates : Continuous radialCoordinates :=
  (continuous_fstC.norm.sub continuous_const).prodMk
    (continuous_sndC.norm.sub continuous_const)

theorem isOpen_phaseDomain : IsOpen phaseDomain :=
  (isOpen_lt continuous_const continuous_fstC.norm).inter
    ((isOpen_lt continuous_fstC.norm continuous_const).inter
      ((isOpen_lt continuous_const continuous_sndC.norm).inter
        (isOpen_lt continuous_sndC.norm continuous_const)))

theorem isCompact_directComb : IsCompact (comb cantorSet gapFunction) :=
  isCompact_comb isCompact_cantorSet continuous_gapFunction

theorem directComb_bounds {p : ℝ × ℝ} (hp : p ∈ comb cantorSet gapFunction) :
    p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (-(1 / 16) : ℝ) 1 := by
  rcases hp with ⟨x, hx, rfl⟩ | ⟨hx, hy⟩
  · exact ⟨hx, by constructor <;>
      nlinarith [gapFunction_nonneg x, gapFunction_le x]⟩
  · exact ⟨cantorSet_subset hx, by constructor <;> linarith [hy.1, hy.2]⟩

theorem directAttractor_subset_phaseDomain : directAttractor ⊆ phaseDomain := by
  intro u hu
  obtain ⟨hx, hy⟩ := directComb_bounds hu
  change 0 ≤ ‖fstC u‖ - 2 ∧ ‖fstC u‖ - 2 ≤ 1 at hx
  change -(1 / 16 : ℝ) ≤ ‖sndC u‖ - 2 ∧ ‖sndC u‖ - 2 ≤ 1 at hy
  change 1 < ‖fstC u‖ ∧ ‖fstC u‖ < 4 ∧ 1 < ‖sndC u‖ ∧ ‖sndC u‖ < 4
  exact ⟨by linarith [hx.1], by linarith [hx.2],
    by linarith [hy.1], by linarith [hy.2]⟩

theorem isClosed_directAttractor : IsClosed directAttractor :=
  isCompact_directComb.isClosed.preimage continuous_radialCoordinates

theorem isCompact_directAttractor : IsCompact directAttractor := by
  apply Metric.isCompact_of_isClosed_isBounded isClosed_directAttractor
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨6, fun u hu => ?_⟩
  obtain ⟨hx, hy⟩ := directComb_bounds hu
  have hnorm := norm_pack_le (fstC u) (sndC u)
  rw [pack_fstC_sndC] at hnorm
  change 0 ≤ ‖fstC u‖ - 2 ∧ ‖fstC u‖ - 2 ≤ 1 at hx
  change -(1 / 16 : ℝ) ≤ ‖sndC u‖ - 2 ∧ ‖sndC u‖ - 2 ≤ 1 at hy
  linarith [hx.2, hy.2]

theorem directAttractor_nonempty : directAttractor.Nonempty := by
  refine ⟨pack 2 2, Or.inr ?_⟩
  change (‖fstC (pack 2 2)‖ - 2 ∈ cantorSet) ∧
    (‖sndC (pack 2 2)‖ - 2 ∈ Icc (0 : ℝ) 1)
  norm_num
  exact zero_mem_cantorSet

theorem phaseDomain_nonempty : phaseDomain.Nonempty :=
  directAttractor_nonempty.mono directAttractor_subset_phaseDomain

theorem directFlow_zero {u : Eden.PhaseSpace 4} (hu : u ∈ phaseDomain) :
    directFlow 0 u = u := by
  have h1 : 2 + (‖fstC u‖ - 2) ≠ 0 := by linarith [hu.1]
  have h2 : 2 + (‖sndC u‖ - 2) ≠ 0 := by linarith [hu.2.2.1]
  simp only [directFlow, combFlow, scalarFlow_zero,
    forcedScalarFlow_zero (gapFunction_nonneg _), div_self h1, div_self h2,
    Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero, one_mul, one_smul,
    pack_fstC_sndC]

theorem scalar_coordinates_fixed {p : ℝ × ℝ}
    (hp : p ∈ comb cantorSet gapFunction) (t : ℝ) :
    scalarFlow t p.1 = p.1 ∧ forcedScalarFlow (gapFunction p.1) t p.2 = p.2 := by
  constructor
  · exact scalarFlow_fixed (directComb_bounds hp).1 t
  · rcases hp with ⟨x, hx, rfl⟩ | ⟨hx, hy⟩
    · exact forcedScalarFlow_graph_fixed (gapFunction_nonneg x) t
    · rw [gapFunction_zero_on_cantor hx]
      exact forcedScalarFlow_tooth_fixed hy t

theorem directFlow_on_attractor {u : Eden.PhaseSpace 4}
    (hu : u ∈ directAttractor) (t : ℝ) :
    directFlow t u = pack (Complex.exp ((t : ℂ) * Complex.I) * fstC u)
      (Complex.exp (((Real.sqrt 2 * t : ℝ) : ℂ) * Complex.I) * sndC u) := by
  obtain ⟨hx, hy⟩ := scalar_coordinates_fixed hu t
  have hU := directAttractor_subset_phaseDomain hu
  have h1 : 2 + (‖fstC u‖ - 2) ≠ 0 := by dsimp [phaseDomain] at hU; linarith [hU.1]
  have h2 : 2 + (‖sndC u‖ - 2) ≠ 0 := by dsimp [phaseDomain] at hU; linarith [hU.2.2.1]
  change scalarFlow t (‖fstC u‖ - 2) = ‖fstC u‖ - 2 at hx
  change forcedScalarFlow (gapFunction (‖fstC u‖ - 2)) t (‖sndC u‖ - 2) =
    ‖sndC u‖ - 2 at hy
  simp only [directFlow, combFlow, hx, hy, div_self h1, div_self h2, one_smul]

theorem directFlow_no_positive_return {u : Eden.PhaseSpace 4}
    (hu : u ∈ directAttractor) {t : ℝ} (ht : 0 < t) : directFlow t u ≠ u := by
  intro hr
  rw [directFlow_on_attractor hu] at hr
  have hU := directAttractor_subset_phaseDomain hu
  have hz : fstC u ≠ 0 := by
    intro h
    have := hU.1
    norm_num [h] at this
  have hw : sndC u ≠ 0 := by
    intro h
    have := hU.2.2.1
    norm_num [h] at this
  have h1 : Complex.exp ((t : ℂ) * Complex.I) = 1 :=
    mul_right_cancel₀ hz (by simpa using congrArg fstC hr)
  have h2 : Complex.exp (((Real.sqrt 2 * t : ℝ) : ℂ) * Complex.I) = 1 :=
    mul_right_cancel₀ hw (by simpa using congrArg sndC hr)
  have hc1 : Real.cos t = 1 := by simpa [Complex.exp_re] using congrArg Complex.re h1
  have hc2 : Real.cos (Real.sqrt 2 * t) = 1 := by
    simpa [Complex.exp_re] using congrArg Complex.re h2
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff t).mp hc1
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (Real.sqrt 2 * t)).mp hc2
  have hm0 : (m : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hm
    linarith
  have hrel : (n : ℝ) = Real.sqrt 2 * (m : ℝ) := by
    apply mul_right_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    calc
      (n : ℝ) * (2 * Real.pi) = Real.sqrt 2 * t := hn
      _ = Real.sqrt 2 * ((m : ℝ) * (2 * Real.pi)) := by rw [hm]
      _ = (Real.sqrt 2 * (m : ℝ)) * (2 * Real.pi) := by ring
  exact irrational_sqrt_two.ne_rational n m ((eq_div_iff hm0).mpr hrel.symm)

theorem directFlow_radialCoordinates {u : Eden.PhaseSpace 4}
    (hu : u ∈ directAttractor) (t : ℝ) :
    radialCoordinates (directFlow t u) = radialCoordinates u := by
  rw [directFlow_on_attractor hu]
  simp only [radialCoordinates, fstC_pack, sndC_pack, norm_mul,
    norm_exp_mul_I, one_mul]

theorem directFlow_mem_attractor {u : Eden.PhaseSpace 4}
    (hu : u ∈ directAttractor) (t : ℝ) : directFlow t u ∈ directAttractor := by
  change radialCoordinates (directFlow t u) ∈ comb cantorSet gapFunction
  rw [directFlow_radialCoordinates hu]
  exact hu

theorem directFlow_add_on_attractor {u : Eden.PhaseSpace 4}
    (hu : u ∈ directAttractor) (s t : ℝ) :
    directFlow s (directFlow t u) = directFlow (s + t) u := by
  rw [directFlow_on_attractor (directFlow_mem_attractor hu t),
    directFlow_on_attractor hu, directFlow_on_attractor hu]
  simp only [fstC_pack, sndC_pack, ← mul_assoc, ← Complex.exp_add]
  congr 2 <;> congr 1 <;> push_cast <;> ring

theorem directFlow_zero_on_attractor {u : Eden.PhaseSpace 4}
    (hu : u ∈ directAttractor) : directFlow 0 u = u := by
  rw [directFlow_on_attractor hu]
  simp

theorem directFlow_image_attractor (t : ℝ) : directFlow t '' directAttractor = directAttractor := by
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact directFlow_mem_attractor hu t
  · intro u hu
    refine ⟨directFlow (-t) u, directFlow_mem_attractor hu (-t), ?_⟩
    rw [directFlow_add_on_attractor hu, add_neg_cancel, directFlow_zero_on_attractor hu]

end Eden.StrangeProof.Direct
