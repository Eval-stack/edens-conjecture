import EdensConjecture.EStatementDefinitions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate

namespace Eden
namespace TorusCounterexample

abbrev X := PhaseSpace 4

/-- The first complex coordinate of `R^4 = C x C`. -/
def fstC (x : X) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I

/-- The second complex coordinate of `R^4 = C x C`. -/
def sndC (x : X) : ℂ := (x 2 : ℂ) + (x 3 : ℂ) * Complex.I

/-- Assemble two complex coordinates into `R^4`. -/
def pack (z w : ℂ) : X := ![z.re, z.im, w.re, w.im]
  |> WithLp.toLp 2

@[simp] lemma fstC_pack (z w : ℂ) : fstC (pack z w) = z := by
  apply Complex.ext <;> simp [fstC, pack]

@[simp] lemma sndC_pack (z w : ℂ) : sndC (pack z w) = w := by
  apply Complex.ext <;> simp [sndC, pack]

@[simp] lemma pack_fstC_sndC (x : X) : pack (fstC x) (sndC x) = x := by
  ext i
  fin_cases i <;> simp [pack, fstC, sndC]

lemma fstC_ne_zero_of_mem {x : X}
    (hx : (1 / 2 : ℝ) < ‖fstC x‖) : fstC x ≠ 0 := by
  intro h
  norm_num [h] at hx

lemma sndC_ne_zero_of_mem {x : X}
    (hx : (1 / 2 : ℝ) < ‖sndC x‖) : sndC x ≠ 0 := by
  intro h
  norm_num [h] at hx

/-- Affine contraction of a positive radius toward one. -/
def radius (t r : ℝ) : ℝ := 1 + (r - 1) * Real.exp (-t)

/-- One attracting rotating plane. -/
def blockFlow (omega t : ℝ) (z : ℂ) : ℂ :=
  ((radius t ‖z‖ / ‖z‖ : ℝ) : ℂ) *
    Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) * z

/-- The vector field generating `blockFlow` away from the origin. -/
def blockField (omega : ℝ) (z : ℂ) : ℂ :=
  (((1 / ‖z‖ - 1 : ℝ) : ℂ) + (omega : ℂ) * Complex.I) * z

/-- The product flow with frequencies `1` and `sqrt 2`. -/
def flow (t : ℝ) (x : X) : X :=
  pack (blockFlow 1 t (fstC x)) (blockFlow (√2) t (sndC x))

/-- Its autonomous vector field. -/
def vectorField (x : X) : X :=
  pack (blockField 1 (fstC x)) (blockField (√2) (sndC x))

/-- A bounded open product of annuli. -/
def U : Set X :=
  {x | (1 / 2 : ℝ) < ‖fstC x‖ ∧ ‖fstC x‖ < 3 / 2 ∧
       (1 / 2 : ℝ) < ‖sndC x‖ ∧ ‖sndC x‖ < 3 / 2}

/-- The invariant two-torus. -/
def K : Set X := {x | ‖fstC x‖ = 1 ∧ ‖sndC x‖ = 1}

lemma radius_zero (r : ℝ) : radius 0 r = r := by
  simp [radius]

lemma radius_add (t s r : ℝ) :
    radius t (radius s r) = radius (t + s) r := by
  simp only [radius, Real.exp_neg, Real.exp_add]
  field_simp
  ring

lemma radius_pos_of_nonneg {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    0 < radius t r := by
  rw [radius]
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  nlinarith

lemma radius_mem_annulus {t r : ℝ} (ht : 0 ≤ t)
    (hl : (1 / 2 : ℝ) < r) (hu : r < 3 / 2) :
    (1 / 2 : ℝ) < radius t r ∧ radius t r < 3 / 2 := by
  have he0 : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  constructor <;> rw [radius] <;> nlinarith

lemma norm_exp_mul_I (a : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

lemma norm_blockFlow {omega t : ℝ} {z : ℂ} (ht : 0 ≤ t) (hz : 0 < ‖z‖) :
    ‖blockFlow omega t z‖ = radius t ‖z‖ := by
  rw [blockFlow, norm_mul, norm_mul, Complex.norm_real, norm_exp_mul_I]
  simp only [mul_one]
  rw [Real.norm_eq_abs,
    abs_of_pos (div_pos (radius_pos_of_nonneg ht hz) hz), div_mul_cancel₀ _ hz.ne']

lemma blockFlow_zero (omega : ℝ) {z : ℂ} (hz : z ≠ 0) :
    blockFlow omega 0 z = z := by
  simp [blockFlow, radius_zero, norm_ne_zero_iff.mpr hz]

lemma blockFlow_add (omega : ℝ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    {z : ℂ} (hz : z ≠ 0) :
    blockFlow omega (t + s) z = blockFlow omega t (blockFlow omega s z) := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrs : 0 < radius s ‖z‖ := radius_pos_of_nonneg hs hz0
  have hbs : blockFlow omega s z ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [norm_blockFlow hs hz0]; exact hrs.ne')
  conv_rhs => rw [blockFlow]
  rw [norm_blockFlow hs hz0]
  simp only [blockFlow]
  have hexp :
      Complex.exp ((((omega * (t + s) : ℝ)) : ℂ) * Complex.I) =
        Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((omega * s : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hexp]
  rw [← radius_add]
  field_simp [norm_ne_zero_iff.mpr hz, hrs.ne', hbs]
  ring_nf
  norm_cast
  field_simp [hz0.ne', hrs.ne']

lemma continuous_fstC : Continuous fstC := by
  unfold fstC
  fun_prop

lemma continuous_sndC : Continuous sndC := by
  unfold sndC
  fun_prop

lemma continuous_pack : Continuous fun p : ℂ × ℂ => pack p.1 p.2 := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp [pack] <;> fun_prop

lemma isOpen_U : IsOpen U := by
  let h1 : IsOpen {x : X | (1 / 2 : ℝ) < ‖fstC x‖} :=
    isOpen_lt continuous_const continuous_fstC.norm
  let h2 : IsOpen {x : X | ‖fstC x‖ < (3 / 2 : ℝ)} :=
    isOpen_lt continuous_fstC.norm continuous_const
  let h3 : IsOpen {x : X | (1 / 2 : ℝ) < ‖sndC x‖} :=
    isOpen_lt continuous_const continuous_sndC.norm
  let h4 : IsOpen {x : X | ‖sndC x‖ < (3 / 2 : ℝ)} :=
    isOpen_lt continuous_sndC.norm continuous_const
  simpa only [U, setOf_and] using h1.inter (h2.inter (h3.inter h4))

lemma nonempty_U : U.Nonempty := by
  refine ⟨pack 1 1, ?_⟩
  norm_num [U]

lemma K_subset_U : K ⊆ U := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  simp only [U, mem_setOf_eq]
  rw [hx1, hx2]
  norm_num

lemma flow_zero {x : X} (hx : x ∈ U) : flow 0 x = x := by
  rcases hx with ⟨hx1, _hx1', hx2, _hx2'⟩
  rw [flow, blockFlow_zero 1 (fstC_ne_zero_of_mem hx1),
    blockFlow_zero (√2) (sndC_ne_zero_of_mem hx2), pack_fstC_sndC]

lemma flow_add {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) {x : X} (hx : x ∈ U) :
    flow (t + s) x = flow t (flow s x) := by
  rcases hx with ⟨hx1, _hx1', hx2, _hx2'⟩
  simp only [flow, fstC_pack, sndC_pack]
  rw [
    ← blockFlow_add 1 ht hs (fstC_ne_zero_of_mem hx1),
    ← blockFlow_add (√2) ht hs (sndC_ne_zero_of_mem hx2)]

lemma flow_mapsTo_U {t : ℝ} (ht : 0 ≤ t) : MapsTo (flow t) U U := by
  intro x hx
  rcases hx with ⟨hx1, hx1', hx2, hx2'⟩
  have hz1 : 0 < ‖fstC x‖ := lt_trans (by norm_num) hx1
  have hz2 : 0 < ‖sndC x‖ := lt_trans (by norm_num) hx2
  simp only [flow, fstC_pack, sndC_pack, U, mem_setOf_eq]
  rw [norm_blockFlow ht hz1, norm_blockFlow ht hz2]
  exact ⟨(radius_mem_annulus ht hx1 hx1').1,
    (radius_mem_annulus ht hx1 hx1').2,
    (radius_mem_annulus ht hx2 hx2').1,
    (radius_mem_annulus ht hx2 hx2').2⟩

lemma radius_one (t : ℝ) : radius t 1 = 1 := by
  simp [radius]

lemma norm_blockFlow_of_norm_one (omega t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖blockFlow omega t z‖ = 1 := by
  unfold blockFlow
  rw [hz, radius_one]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp]
  simp
  exact hz

lemma blockFlow_of_norm_one (omega t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    blockFlow omega t z = Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) * z := by
  simp [blockFlow, hz, radius_one]

lemma flow_mapsTo_K (t : ℝ) : MapsTo (flow t) K K := by
  intro x hx
  rcases hx with ⟨hx1, hx2⟩
  simp only [flow, fstC_pack, sndC_pack, K, mem_setOf_eq]
  exact ⟨norm_blockFlow_of_norm_one 1 t hx1,
    norm_blockFlow_of_norm_one (√2) t hx2⟩

lemma blockFlow_neg_comp_of_norm_one (omega t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    blockFlow omega t (blockFlow omega (-t) z) = z := by
  rw [blockFlow_of_norm_one omega (-t) hz]
  have hn : ‖Complex.exp ((((omega * -t : ℝ)) : ℂ) * Complex.I) * z‖ = 1 := by
    rw [norm_mul, Complex.norm_exp, hz]
    simp
  rw [blockFlow_of_norm_one omega t hn]
  rw [← mul_assoc, ← Complex.exp_add]
  convert one_mul z using 1 <;> push_cast <;> ring_nf <;> simp

lemma flow_neg_comp_on_K (t : ℝ) {x : X} (hx : x ∈ K) :
    flow t (flow (-t) x) = x := by
  rcases hx with ⟨hx1, hx2⟩
  simp only [flow, fstC_pack, sndC_pack]
  rw [blockFlow_neg_comp_of_norm_one 1 t hx1,
    blockFlow_neg_comp_of_norm_one (√2) t hx2, pack_fstC_sndC]

lemma flow_image_K (t : ℝ) : flow t '' K = K := by
  apply Set.Subset.antisymm
  · exact (flow_mapsTo_K t).image_subset
  · intro x hx
    refine ⟨flow (-t) x, flow_mapsTo_K (-t) hx, ?_⟩
    exact flow_neg_comp_on_K t hx

def unitCircle : Set ℂ := {z | ‖z‖ = 1}

lemma isCompact_unitCircle : IsCompact unitCircle := by
  have h := isCompact_sphere (0 : ℂ) 1
  simpa [unitCircle, Metric.sphere, dist_zero_right] using h

lemma K_eq_pack_image : K = (fun p : ℂ × ℂ => pack p.1 p.2) '' (unitCircle ×ˢ unitCircle) := by
  ext x
  constructor
  · intro hx
    refine ⟨(fstC x, sndC x), ?_, pack_fstC_sndC x⟩
    exact hx
  · rintro ⟨⟨z, w⟩, ⟨hz, hw⟩, rfl⟩
    exact ⟨by simpa [unitCircle] using hz, by simpa [unitCircle] using hw⟩

lemma isCompact_K : IsCompact K := by
  rw [K_eq_pack_image]
  exact (isCompact_unitCircle.prod isCompact_unitCircle).image continuous_pack

lemma nonempty_K : K.Nonempty := by
  refine ⟨pack 1 1, ?_⟩
  norm_num [K]

lemma block_multiplier_eq_one_of_return (omega T : ℝ) {z : ℂ}
    (hz : ‖z‖ = 1) (hreturn : blockFlow omega T z = z) :
    Complex.exp (((omega * T : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [blockFlow_of_norm_one omega T hz] at hreturn
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  exact mul_right_cancel₀ hz0 (by simpa using hreturn)

lemma cos_eq_one_of_block_return (omega T : ℝ) {z : ℂ}
    (hz : ‖z‖ = 1) (hreturn : blockFlow omega T z = z) :
    Real.cos (omega * T) = 1 := by
  have h := block_multiplier_eq_one_of_return omega T hz hreturn
  have hre := congrArg Complex.re h
  simpa [Complex.exp_re] using hre

lemma no_positive_return {x : X} (hx : x ∈ K) {T : ℝ} (hT : 0 < T) :
    flow T x ≠ x := by
  intro hreturn
  rcases hx with ⟨hx1, hx2⟩
  have hreturn1 : blockFlow 1 T (fstC x) = fstC x := by
    simpa only [flow, fstC_pack] using congrArg fstC hreturn
  have hreturn2 : blockFlow (√2) T (sndC x) = sndC x := by
    simpa only [flow, sndC_pack] using congrArg sndC hreturn
  have hc1 : Real.cos T = 1 := by
    simpa using cos_eq_one_of_block_return 1 T hx1 hreturn1
  have hc2 : Real.cos (√2 * T) = 1 :=
    cos_eq_one_of_block_return (√2) T hx2 hreturn2
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff T).mp hc1
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (√2 * T)).mp hc2
  have hm0r : (m : ℝ) ≠ 0 := by
    intro hm0
    rw [hm0, zero_mul] at hm
    linarith
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hrel : (n : ℝ) = √2 * (m : ℝ) := by
    apply mul_right_cancel₀ htwoPi
    calc
      (n : ℝ) * (2 * Real.pi) = √2 * T := hn
      _ = √2 * ((m : ℝ) * (2 * Real.pi)) := by rw [hm]
      _ = (√2 * (m : ℝ)) * (2 * Real.pi) := by ring
  have hsqrt : (√2 : ℝ) = (n : ℝ) / (m : ℝ) := by
    rw [eq_div_iff hm0r]
    exact hrel.symm
  exact irrational_sqrt_two.ne_rational n m hsqrt

lemma no_stationary_on_K {x : X} (hx : x ∈ K) :
    ¬ StationarySolution flow x := by
  intro h
  exact no_positive_return hx one_pos (h 1 zero_le_one)

lemma no_periodic_on_K {x : X} (hx : x ∈ K) :
    ¬ PeriodicSolution flow x := by
  rintro ⟨_hnotstat, T, hT, hperiod⟩
  apply no_positive_return hx hT
  simpa [flow_zero (K_subset_U hx)] using hperiod 0 le_rfl

lemma norm_pack_sq (z w : ℂ) :
    ‖pack z w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [pack, Fin.sum_univ_succ, Complex.sq_norm, Complex.normSq_apply]
  ring

lemma norm_pack_le (z w : ℂ) : ‖pack z w‖ ≤ ‖z‖ + ‖w‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [norm_pack_sq]
  nlinarith [mul_nonneg (norm_nonneg z) (norm_nonneg w)]

lemma pack_sub (z₁ z₂ w₁ w₂ : ℂ) :
    pack z₁ w₁ - pack z₂ w₂ = pack (z₁ - z₂) (w₁ - w₂) := by
  ext i
  fin_cases i <;> simp [pack]

def circlePoint (omega t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) * ((‖z‖⁻¹ : ℝ) • z)

lemma norm_circlePoint {omega t : ℝ} {z : ℂ} (hz : 0 < ‖z‖) :
    ‖circlePoint omega t z‖ = 1 := by
  rw [circlePoint, norm_mul, norm_exp_mul_I, one_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr hz), inv_mul_cancel₀ hz.ne']

lemma blockFlow_sub_circlePoint_norm {omega t : ℝ} {z : ℂ}
    (ht : 0 ≤ t) (hz : 0 < ‖z‖) :
    ‖blockFlow omega t z - circlePoint omega t z‖ =
      |radius t ‖z‖ - 1| := by
  have hz0 : ‖z‖ ≠ 0 := hz.ne'
  rw [blockFlow, circlePoint]
  have halg :
      ((radius t ‖z‖ / ‖z‖ : ℝ) : ℂ) *
          Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) * z -
        Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) * ((‖z‖⁻¹ : ℝ) • z) =
      (((radius t ‖z‖ - 1) / ‖z‖ : ℝ) : ℂ) *
          Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) * z := by
    simp only [Complex.real_smul]
    push_cast
    field_simp [hz0]
  rw [halg, norm_mul, norm_mul, Complex.norm_real, Complex.norm_exp]
  rw [show Real.exp
      ((((omega * t : ℝ) : ℂ) * Complex.I).re) = 1 by simp]
  simp only [mul_one]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hz, div_mul_cancel₀ _ hz0]

lemma abs_radius_sub_one_lt {t r : ℝ} (ht : 0 ≤ t)
    (hl : (1 / 2 : ℝ) < r) (hu : r < 3 / 2) :
    |radius t r - 1| < (1 / 2 : ℝ) * Real.exp (-t) := by
  have hr : |r - 1| < (1 / 2 : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  rw [radius]
  simp only [add_sub_cancel_left, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_lt_mul_of_pos_right hr (Real.exp_pos _)

def comparisonPoint (t : ℝ) (x : X) : X :=
  pack (circlePoint 1 t (fstC x)) (circlePoint (√2) t (sndC x))

lemma comparisonPoint_mem_K {t : ℝ} {x : X} (hx : x ∈ U) :
    comparisonPoint t x ∈ K := by
  rcases hx with ⟨hx1, _hx1', hx2, _hx2'⟩
  have hz1 : 0 < ‖fstC x‖ := lt_trans (by norm_num) hx1
  have hz2 : 0 < ‖sndC x‖ := lt_trans (by norm_num) hx2
  exact ⟨by simpa [comparisonPoint] using
      (norm_circlePoint (omega := 1) (t := t) hz1),
    by simpa [comparisonPoint] using
      (norm_circlePoint (omega := √2) (t := t) hz2)⟩

lemma dist_flow_comparison_lt {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ U) :
    dist (flow t x) (comparisonPoint t x) < Real.exp (-t) := by
  rcases hx with ⟨hx1, hx1', hx2, hx2'⟩
  have hz1 : 0 < ‖fstC x‖ := lt_trans (by norm_num) hx1
  have hz2 : 0 < ‖sndC x‖ := lt_trans (by norm_num) hx2
  rw [dist_eq_norm, flow, comparisonPoint, pack_sub]
  refine (norm_pack_le _ _).trans_lt ?_
  rw [blockFlow_sub_circlePoint_norm ht hz1,
    blockFlow_sub_circlePoint_norm ht hz2]
  have h1 := abs_radius_sub_one_lt ht hx1 hx1'
  have h2 := abs_radius_sub_one_lt ht hx2 hx2'
  linarith

lemma uniformlyAttracts_K (B : Set X) (hBU : B ⊆ U) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T : ℝ, 0 ≤ T ∧
        ∀ t : ℝ, T ≤ t → ∀ u ∈ B,
          ∃ v ∈ K, dist (flow t u) v < ε := by
  intro ε hε
  refine ⟨max 0 (-Real.log ε), le_max_left _ _, ?_⟩
  intro t ht u hu
  have ht0 : 0 ≤ t := (le_max_left 0 (-Real.log ε)).trans ht
  have het : Real.exp (-t) ≤ ε := by
    rw [← Real.exp_log hε, Real.exp_le_exp]
    have := (le_max_right 0 (-Real.log ε)).trans ht
    linarith
  refine ⟨comparisonPoint t u, comparisonPoint_mem_K (hBU hu), ?_⟩
  exact (dist_flow_comparison_lt ht0 (hBU hu)).trans_le het

lemma contDiff_fstC : ContDiff ℝ ⊤ fstC := by
  unfold fstC
  change ContDiff ℝ ⊤
    (fun x : X => Complex.ofRealCLM (x 0) + Complex.ofRealCLM (x 1) * Complex.I)
  fun_prop

lemma contDiff_sndC : ContDiff ℝ ⊤ sndC := by
  unfold sndC
  change ContDiff ℝ ⊤
    (fun x : X => Complex.ofRealCLM (x 2) + Complex.ofRealCLM (x 3) * Complex.I)
  fun_prop

lemma contDiff_pack : ContDiff ℝ ⊤ (fun p : ℂ × ℂ => pack p.1 p.2) := by
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ => Complex.reCLM p.1)
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ => Complex.imCLM p.1)
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ => Complex.reCLM p.2)
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ => Complex.imCLM p.2)
    fun_prop

lemma contDiffAt_blockField (omega : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ 1 (blockField omega) z := by
  have hn : ContDiffAt ℝ 1 (fun z : ℂ => ‖z‖) z :=
    contDiffAt_norm ℝ hz
  have hreal : ContDiffAt ℝ 1 (fun z : ℂ => 1 / ‖z‖ - 1) z :=
    (contDiffAt_const.div hn (norm_ne_zero_iff.mpr hz)).sub contDiffAt_const
  have hcoe : ContDiffAt ℝ 1
      (fun z : ℂ => Complex.ofRealCLM (1 / ‖z‖ - 1)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hreal
  have hconst : ContDiffAt ℝ 1
      (fun _ : ℂ => (omega : ℂ) * Complex.I) z := contDiffAt_const
  have h : ContDiffAt ℝ 1
      (fun z : ℂ =>
        (Complex.ofRealCLM (1 / ‖z‖ - 1) + (omega : ℂ) * Complex.I) * z) z :=
    (hcoe.add hconst).mul contDiffAt_id
  convert h using 1 <;> rfl

lemma contDiffAt_blockFlow (omega t : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ 1 (blockFlow omega t) z := by
  have hn : ContDiffAt ℝ 1 (fun z : ℂ => ‖z‖) z :=
    contDiffAt_norm ℝ hz
  have hreal : ContDiffAt ℝ 1
      (fun z : ℂ => (1 + (‖z‖ - 1) * Real.exp (-t)) / ‖z‖) z :=
    (contDiffAt_const.add ((hn.sub contDiffAt_const).mul contDiffAt_const)).div
      hn (norm_ne_zero_iff.mpr hz)
  have hcoe : ContDiffAt ℝ 1
      (fun z : ℂ =>
        Complex.ofRealCLM ((1 + (‖z‖ - 1) * Real.exp (-t)) / ‖z‖)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hreal
  have hconst : ContDiffAt ℝ 1
      (fun _ : ℂ => Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I)) z :=
    contDiffAt_const
  have h : ContDiffAt ℝ 1
      (fun z : ℂ =>
        Complex.ofRealCLM ((1 + (‖z‖ - 1) * Real.exp (-t)) / ‖z‖) *
          Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) * z) z :=
    (hcoe.mul hconst).mul contDiffAt_id
  convert h using 1 <;> rfl

lemma vectorField_contDiffOn : ContDiffOn ℝ 1 vectorField U := by
  intro x hx
  rcases hx with ⟨hx1, _hx1', hx2, _hx2'⟩
  have hz1 := fstC_ne_zero_of_mem hx1
  have hz2 := sndC_ne_zero_of_mem hx2
  have hp : ContDiffAt ℝ 1
      (fun x : X => (blockField 1 (fstC x), blockField (√2) (sndC x))) x := by
    apply ContDiffAt.prodMk
    · exact (contDiffAt_blockField 1 hz1).comp x
        (contDiff_fstC.of_le (by simp)).contDiffAt
    · exact (contDiffAt_blockField (√2) hz2).comp x
        (contDiff_sndC.of_le (by simp)).contDiffAt
  have hpack : ContDiff ℝ 1 (fun p : ℂ × ℂ => pack p.1 p.2) :=
    contDiff_pack.of_le (by simp)
  have h := hpack.contDiffAt.comp x hp
  convert h.contDiffWithinAt using 1 <;> rfl

lemma flow_contDiffOn (t : ℝ) : ContDiffOn ℝ 1 (flow t) U := by
  intro x hx
  rcases hx with ⟨hx1, _hx1', hx2, _hx2'⟩
  have hz1 := fstC_ne_zero_of_mem hx1
  have hz2 := sndC_ne_zero_of_mem hx2
  have hp : ContDiffAt ℝ 1
      (fun x : X => (blockFlow 1 t (fstC x), blockFlow (√2) t (sndC x))) x := by
    apply ContDiffAt.prodMk
    · exact (contDiffAt_blockFlow 1 t hz1).comp x
        (contDiff_fstC.of_le (by simp)).contDiffAt
    · exact (contDiffAt_blockFlow (√2) t hz2).comp x
        (contDiff_sndC.of_le (by simp)).contDiffAt
  have hpack : ContDiff ℝ 1 (fun p : ℂ × ℂ => pack p.1 p.2) :=
    contDiff_pack.of_le (by simp)
  have h := hpack.contDiffAt.comp x hp
  convert h.contDiffWithinAt using 1 <;> rfl

lemma continuousAt_jointFlow {p : ℝ × X} (hp : p ∈ (Ici 0) ×ˢ U) :
    ContinuousAt (fun q : ℝ × X => flow q.1 q.2) p := by
  rcases hp.2 with ⟨hp1, _hp1', hp2, _hp2'⟩
  have hz1 := fstC_ne_zero_of_mem hp1
  have hz2 := sndC_ne_zero_of_mem hp2
  have htime : Continuous (fun q : ℝ × X => q.1) := continuous_fst
  have hfst : Continuous (fun q : ℝ × X => fstC q.2) :=
    contDiff_fstC.continuous.comp continuous_snd
  have hsnd : Continuous (fun q : ℝ × X => sndC q.2) :=
    contDiff_sndC.continuous.comp continuous_snd
  have hblock (omega : ℝ) (coord : X → ℂ)
      (hcoord : Continuous coord) (hz : coord p.2 ≠ 0) :
      ContinuousAt (fun q : ℝ × X => blockFlow omega q.1 (coord q.2)) p := by
    have hc : Continuous (fun q : ℝ × X => coord q.2) :=
      hcoord.comp continuous_snd
    have hn : Continuous (fun q : ℝ × X => ‖coord q.2‖) := hc.norm
    have he : Continuous (fun q : ℝ × X => Real.exp (-q.1)) :=
      Real.continuous_exp.comp htime.neg
    have hr : Continuous (fun q : ℝ × X =>
        1 + (‖coord q.2‖ - 1) * Real.exp (-q.1)) :=
      continuous_const.add ((hn.sub continuous_const).mul he)
    have hquot : ContinuousAt (fun q : ℝ × X =>
        (1 + (‖coord q.2‖ - 1) * Real.exp (-q.1)) / ‖coord q.2‖) p :=
      hr.continuousAt.div hn.continuousAt (norm_ne_zero_iff.mpr hz)
    have hquotC : ContinuousAt (fun q : ℝ × X =>
        Complex.ofRealCLM
          ((1 + (‖coord q.2‖ - 1) * Real.exp (-q.1)) / ‖coord q.2‖)) p :=
      Complex.ofRealCLM.continuous.continuousAt.comp hquot
    have hphase : Continuous (fun q : ℝ × X =>
        Complex.exp (((omega * q.1 : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have h := (hquotC.mul hphase.continuousAt).mul hc.continuousAt
    convert h using 1 <;> rfl
  have hpairs : ContinuousAt
      (fun q : ℝ × X =>
        (blockFlow 1 q.1 (fstC q.2), blockFlow (√2) q.1 (sndC q.2))) p := by
    apply ContinuousAt.prodMk
    · exact hblock 1 fstC contDiff_fstC.continuous hz1
    · exact hblock (√2) sndC contDiff_sndC.continuous hz2
  have h := continuous_pack.continuousAt.comp hpairs
  convert h using 1 <;> rfl

lemma flow_continuousOn :
    ContinuousOn (fun p : ℝ × X => flow p.1 p.2) ((Ici 0) ×ˢ U) := by
  intro p hp
  exact (continuousAt_jointFlow hp).continuousWithinAt

lemma hasDerivAt_radius (t r : ℝ) :
    HasDerivAt (fun s : ℝ => radius s r) (1 - radius t r) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg using 1 <;> first | rfl | ring
  have h := (hasDerivAt_const t (1 : ℝ)).add
    ((hasDerivAt_const t (r - 1)).mul he)
  convert h using 1 <;> first | rfl | (dsimp [radius]; ring)

lemma hasDerivAt_blockFlow (omega : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : 0 < ‖z‖) :
    HasDerivAt (fun s : ℝ => blockFlow omega s z)
      (blockField omega (blockFlow omega t z)) t := by
  have hr := (hasDerivAt_radius t ‖z‖).ofReal_comp
  have hlin : HasDerivAt (fun s : ℝ => ((omega * s : ℝ) : ℂ)) (omega : ℂ) t :=
    by simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul omega).ofReal_comp
  have hphase : HasDerivAt
      (fun s : ℝ => Complex.exp (((omega * s : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I) *
        ((omega : ℂ) * Complex.I)) t :=
    (hlin.mul_const Complex.I).cexp
  have hscale : HasDerivAt
      (fun s : ℝ => ((radius s ‖z‖ / ‖z‖ : ℝ) : ℂ))
      (((1 - radius t ‖z‖) / ‖z‖ : ℝ) : ℂ) t := by
    convert hr.div_const (‖z‖ : ℂ) using 1 <;> first | rfl | (push_cast; rfl)
  have hraw := (hscale.mul hphase).mul_const z
  convert hraw using 1 <;> first | rfl | skip
  · rw [blockField, norm_blockFlow ht hz]
    unfold blockFlow
    push_cast
    field_simp [ne_of_gt hz, ne_of_gt (radius_pos_of_nonneg ht hz)]

lemma flow_solves_ODE (u : X) (hu : u ∈ U) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => flow s u) (vectorField (flow t u)) (Ici 0) t := by
  rcases hu with ⟨hu1, _hu1', hu2, _hu2'⟩
  have hz1 : 0 < ‖fstC u‖ := lt_trans (by norm_num) hu1
  have hz2 : 0 < ‖sndC u‖ := lt_trans (by norm_num) hu2
  have h1 := hasDerivAt_blockFlow 1 ht hz1
  have h2 := hasDerivAt_blockFlow (√2) ht hz2
  have hp : HasDerivAt
      (fun s : ℝ => pack (blockFlow 1 s (fstC u)) (blockFlow (√2) s (sndC u)))
      (pack (blockField 1 (blockFlow 1 t (fstC u)))
        (blockField (√2) (blockFlow (√2) t (sndC u)))) t := by
    have hraw : HasDerivAt
        (fun s : ℝ =>
          ![(blockFlow 1 s (fstC u)).re, (blockFlow 1 s (fstC u)).im,
            (blockFlow (√2) s (sndC u)).re, (blockFlow (√2) s (sndC u)).im])
        ![(blockField 1 (blockFlow 1 t (fstC u))).re,
          (blockField 1 (blockFlow 1 t (fstC u))).im,
          (blockField (√2) (blockFlow (√2) t (sndC u))).re,
          (blockField (√2) (blockFlow (√2) t (sndC u))).im] t := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
      · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h1
      · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h2
      · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h2
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hraw
  simpa only [flow, vectorField, fstC_pack, sndC_pack] using hp.hasDerivWithinAt

end TorusCounterexample
end Eden
