import EdensConjecture.EMainProofFlow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate
namespace Eden.PolynomialCounterexample

lemma contDiff_jointPhase (omega : ℝ) : ContDiff ℝ ⊤ (fun p : ℝ × ℂ => phase omega p.1) := by
  unfold phase
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_fst)).mul contDiff_const)

lemma contDiffAt_jointBlockFlow (omega : ℝ) (p : ℝ × ℂ)
    (hd : 0 < radialDenominator p.1 (‖p.2‖ ^ 2 - 1)) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × ℂ => blockFlow omega q.1 q.2) p := by
  have hq : ContDiff ℝ ⊤ (fun q : ℝ × ℂ => ‖q.2‖ ^ 2) := (contDiff_norm_sq ℂ).comp contDiff_snd
  have he : ContDiff ℝ ⊤ (fun q : ℝ × ℂ => Real.exp (-4 * q.1)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
  have hden : ContDiff ℝ ⊤ (fun q : ℝ × ℂ => radialDenominator q.1 (‖q.2‖ ^ 2 - 1)) := by
    unfold radialDenominator
    exact ((hq.sub contDiff_const).pow 2).add
      ((contDiff_const.sub ((hq.sub contDiff_const).pow 2)).mul he)
  have hs := hden.contDiffAt.sqrt hd.ne'
  have hspos := Real.sqrt_pos.mpr hd
  by_cases hz : p.2 = 0
  · have hreg : ContDiffAt ℝ ⊤ (fun q : ℝ × ℂ => regularScaleSq q.1 (‖q.2‖ ^ 2)) p := by
      unfold regularScaleSq
      apply ((contDiffAt_const.sub hq.contDiffAt).mul he.contDiffAt).div
        (hs.mul (hs.sub (hq.contDiffAt.sub contDiffAt_const)))
      simp [hz, radialDenominator]
    have hpos : 0 < regularScaleSq p.1 (‖p.2‖ ^ 2) := by
      simp [hz, regularScaleSq, radialDenominator, Real.exp_pos]
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp p (hreg.sqrt hpos.ne')
    have hh := (hc.mul (contDiff_jointPhase omega).contDiffAt).mul contDiffAt_snd
    apply hh.congr_of_eventuallyEq
    have he₁ : ∀ᶠ q : ℝ × ℂ in 𝓝 p, 0 < radialDenominator q.1 (‖q.2‖ ^ 2 - 1) :=
      (isOpen_lt continuous_const hden.continuous).mem_nhds hd
    have he₂ : ∀ᶠ q : ℝ × ℂ in 𝓝 p, ‖q.2‖ ^ 2 < 1 :=
      (isOpen_lt hq.continuous continuous_const).mem_nhds (by simp [hz])
    filter_upwards [he₁, he₂] with q h₁ h₂
    exact blockFlow_eq_regular_of_denominator omega h₁ h₂
  · have hn := norm_pos_iff.mpr hz
    have hrad := (contDiffAt_const.add ((hq.contDiffAt.sub contDiffAt_const).div hs hspos.ne')).sqrt
      (squaredRadius_pos_of_denominator hd (sq_pos_of_pos hn)).ne'
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp p
      (hrad.div ((contDiffAt_norm ℝ hz).comp p contDiffAt_snd) hn.ne')
    have hh := (hc.mul (contDiff_jointPhase omega).contDiffAt).mul contDiffAt_snd
    convert hh using 1 <;> rfl

lemma contDiffAt_jointFlow (p : ℝ × X) (ht : 0 ≤ p.1) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × X => flow q.1 q.2) p := by
  have h₁ := (contDiffAt_jointBlockFlow 1 (p.1, fstC p.2)
    (radialDenominator_pos ht _)).comp p
      (contDiffAt_fst.prodMk (contDiff_fstC.contDiffAt.comp p contDiffAt_snd))
  have h₂ := (contDiffAt_jointBlockFlow (Real.sqrt 2) (p.1, sndC p.2)
    (radialDenominator_pos ht _)).comp p
      (contDiffAt_fst.prodMk (contDiff_sndC.contDiffAt.comp p contDiffAt_snd))
  have hv : ContDiffAt ℝ ⊤ (fun q : ℝ × X => Real.exp (-8 * q.1) * q.2 4) p := by
    fun_prop
  have hh := contDiff_pack.contDiffAt.comp p (h₁.prodMk (h₂.prodMk hv))
  convert hh using 1 <;> rfl

lemma continuousAt_jointDerivative (p : ℝ × X) (ht : 0 ≤ p.1) :
    ContinuousAt (fun q : ℝ × X => fderiv ℝ (flow q.1) q.2) p := by
  have h := (contDiffAt_jointFlow p ht).comp (p, p.2)
    ((contDiffAt_fst.fst).prodMk contDiffAt_snd)
  exact (h.fderiv (m := 0) contDiffAt_snd (by simp)).continuousAt

lemma continuousOn_jointDerivative :
    ContinuousOn (fun p : ℝ × X => fderiv ℝ (flow p.1) p.2) (Ici 0 ×ˢ K) := by
  intro p hp
  exact (continuousAt_jointDerivative p hp.1).continuousWithinAt

lemma derivative_cocycle {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : X) :
    fderiv ℝ (flow (t + s)) x = (fderiv ℝ (flow t) (flow s x)).comp (fderiv ℝ (flow s) x) := by
  have heq : flow (t + s) = (flow t) ∘ (flow s) := funext fun y => (flow_comp ht hs y).symm
  rw [heq]
  exact fderiv_comp x ((contDiff_flow ht).differentiable (by simp) _)
    ((contDiff_flow hs).differentiable (by simp) _)

lemma derivative_short_time_bound : ∃ M : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
    ∀ x ∈ K, ‖fderiv ℝ (flow t) x‖ ≤ M := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod isCompact_K
  have hcont := continuousOn_jointDerivative.mono
    (show Icc (0 : ℝ) 1 ×ˢ K ⊆ Ici 0 ×ˢ K from fun _ hp => ⟨hp.1.1, hp.2⟩)
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn hcont
  exact ⟨M, fun t ht ht₁ x hx => hM (t, x) ⟨⟨ht.le, ht₁⟩, hx⟩⟩

lemma finiteDimensional_CC {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (A : H →L[ℝ] H) : CCOperator A := by
  refine ⟨A, 0, by simp, ?_, by simp⟩
  exact ((isCompact_closedBall (0 : H) 1).image A.continuous).closure

lemma compact_smooth_remainder {H G : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : H → G} (hf : ContDiff ℝ ⊤ f)
    {A : Set H} (hA : IsCompact A) (hconv : Convex ℝ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ A, ∀ y ∈ A,
      ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hf₁ : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by simp)
  obtain ⟨C₀, hC₀⟩ := hA.exists_bound_of_continuousOn (hf₁.continuous_fderiv (by norm_num)).continuousOn
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound : ∀ x ∈ A, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C :=
    fun x hx => (hC₀ x hx).trans (le_max_left _ _)
  have hLip : ∀ x ∈ A, ∀ y ∈ A, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
    intro x hx y hy
    exact hconv.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf₁.differentiable (by norm_num) z) hbound hx hy
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  let g : H → G := fun z => f z - f x - fderiv ℝ f x (z - x)
  have hg : ∀ z : H, HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f x) z := by
    intro z
    have hh := ((hf.differentiable (by simp) z).hasFDerivAt.sub_const (f x)).sub
      ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
    convert hh using 1 <;> ext v <;> simp [g]
  have hseg := hconv.segment_subset hx hy
  have hgBound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖y - x‖ := by
    intro z hz
    exact (hLip x hx z (hseg hz)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hC)
  have hh := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hg z).hasFDerivWithinAt) hgBound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [g, pow_two, mul_assoc] using hh

lemma norm_le_two_of_mem_K {x : X} (hx : x ∈ K) : ‖x‖ ≤ 2 := by
  have hn := norm_pack_sq (fstC x) (sndC x) (x 4)
  rw [pack_coordinates, norm_fstC_sq, norm_sndC_sq, hx.2.2] at hn
  have hnorm := norm_nonneg x
  nlinarith [hx.1, hx.2.1]

lemma flow_remainder_bound {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖flow t y - flow t x - fderiv ℝ (flow t) x (y - x)‖ ≤ C * ‖y - x‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := compact_smooth_remainder (contDiff_flow ht)
    (isCompact_closedBall (0 : X) 2) (convex_closedBall (0 : X) 2)
  refine ⟨C, hC, fun x hx y hy => hbound x ?_ y ?_⟩
  · simpa using norm_le_two_of_mem_K hx
  · simpa using norm_le_two_of_mem_K hy

end Eden.PolynomialCounterexample
