import EdensConjecture.EMainProofSpectral

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate
namespace Eden.PolynomialCounterexample

def radialJacobian (t q : ℝ) : ℝ :=
  Real.exp (-4 * t) / (Real.sqrt (radialDenominator t (q - 1))) ^ 3

lemma radialJacobian_pos {t : ℝ} (ht : 0 ≤ t) (q : ℝ) : 0 < radialJacobian t q := by
  exact div_pos (Real.exp_pos _) (pow_pos (Real.sqrt_pos.mpr (radialDenominator_pos ht _)) 3)

lemma radialDenominator_bounds {t q : ℝ} (ht : 0 ≤ t) (hq : q ∈ Icc (0 : ℝ) 2) :
    Real.exp (-4 * t) ≤ radialDenominator t (q - 1) ∧ radialDenominator t (q - 1) ≤ 1 := by
  have he : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hsq : (q - 1) ^ 2 ≤ 1 := by nlinarith [hq.1, hq.2]
  unfold radialDenominator
  constructor <;> nlinarith [sq_nonneg (q - 1), mul_nonneg (sq_nonneg (q - 1)) (sub_nonneg.mpr he),
    mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr he)]

lemma radialJacobian_bounds {t q : ℝ} (ht : 0 ≤ t) (hq : q ∈ Icc (0 : ℝ) 2) :
    Real.exp (-4 * t) ≤ radialJacobian t q ∧ radialJacobian t q ≤ Real.exp (2 * t) := by
  obtain ⟨hlo, hhi⟩ := radialDenominator_bounds ht hq
  have hspos := Real.sqrt_pos.mpr (radialDenominator_pos ht (q - 1))
  have hslo : Real.exp (-2 * t) ≤ Real.sqrt (radialDenominator t (q - 1)) := by
    have hh := Real.sqrt_le_sqrt hlo
    rw [show -4 * t = 2 * (-2 * t) by ring, sqrt_exp_double] at hh
    exact hh
  have hshi : Real.sqrt (radialDenominator t (q - 1)) ≤ 1 := by simpa using Real.sqrt_le_sqrt hhi
  have hpHi : Real.sqrt (radialDenominator t (q - 1)) ^ 3 ≤ 1 := by nlinarith [sq_nonneg (1 - Real.sqrt (radialDenominator t (q - 1)))]
  have hpLo : Real.exp (-6 * t) ≤ Real.sqrt (radialDenominator t (q - 1)) ^ 3 := by
    have hh := pow_le_pow_left₀ (Real.exp_pos (-2 * t)).le hslo 3
    have he : Real.exp (-2 * t) ^ 3 = Real.exp (-6 * t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rwa [he] at hh
  unfold radialJacobian
  constructor
  · apply (le_div_iff₀ (pow_pos hspos 3)).mpr
    exact (mul_le_mul_of_nonneg_left hpHi (Real.exp_pos _).le).trans_eq (mul_one _)
  · apply (div_le_iff₀ (pow_pos hspos 3)).mpr
    calc
      Real.exp (-4 * t) = Real.exp (2 * t) * Real.exp (-6 * t) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpLo (Real.exp_pos _).le

lemma positiveScale_bounds {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) (hq₂ : q ≤ 2) :
    Real.exp (-2 * t) ≤ positiveScale t q ∧ positiveScale t q ≤ Real.exp t := by
  obtain ⟨r, hr, heq⟩ := exists_deriv_eq_slope (squaredRadius t) hq
    (contDiff_squaredRadius ht).continuous.continuousOn
    ((contDiff_squaredRadius ht).differentiable (by simp)).differentiableOn
  rw [(hasDerivAt_squaredRadius_initial ht r).deriv] at heq
  have hb := radialJacobian_bounds ht (show r ∈ Icc (0 : ℝ) 2 from ⟨hr.1.le, hr.2.le.trans hq₂⟩)
  change Real.exp (-4 * t) ≤ radialJacobian t r ∧ radialJacobian t r ≤ Real.exp (2 * t) at hb
  have hval : radialJacobian t r = squaredRadius t q / q := by simpa [radialJacobian] using heq
  rw [hval] at hb
  constructor
  · have hh := Real.sqrt_le_sqrt hb.1
    rw [show -4 * t = 2 * (-2 * t) by ring, sqrt_exp_double] at hh
    exact hh
  · simpa [positiveScale, sqrt_exp_double] using Real.sqrt_le_sqrt hb.2

def decreasingPermutation (c : Fin 5 → ℝ) : Equiv.Perm (Fin 5) :=
  (Fin.revPerm).trans (Tuple.sort c)

def decreasingValues (c : Fin 5 → ℝ) (i : Fin 5) : ℝ := c (decreasingPermutation c i)

lemma decreasingValues_antitone (c : Fin 5 → ℝ) : Antitone (decreasingValues c) := by
  intro i j hij
  exact Tuple.monotone_sort c (Fin.rev_le_rev.mpr hij)

lemma singularValues_eq_decreasing (A : X →ₗ[ℝ] X) (c : Fin 5 → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hchar : (A.adjoint.comp A).charpoly = ∏ i : Fin 5, (Polynomial.X - Polynomial.C (c i ^ 2)))
    (i : Fin 5) : A.singularValues i = decreasingValues c i := by
  apply singularValues_eq_of_charpoly A (decreasingValues c)
    (fun j => hc (decreasingPermutation c j)) (decreasingValues_antitone c)
  rw [hchar]
  exact (Equiv.prod_comp (decreasingPermutation c) (fun j => Polynomial.X - Polynomial.C (c j ^ 2))).symm

lemma prod_decreasingValues (c : Fin 5 → ℝ) : ∏ i, decreasingValues c i = ∏ i, c i :=
  Equiv.prod_comp (decreasingPermutation c) c

lemma decreasingValues_last (c : Fin 5 → ℝ) (hc : ∀ i, c 4 ≤ c i) : decreasingValues c 4 = c 4 := by
  apply le_antisymm
  · have hh := Tuple.monotone_sort c (show (0 : Fin 5) ≤ (Tuple.sort c).symm 4 from Fin.zero_le _)
    simpa [Function.comp_def, decreasingValues, decreasingPermutation] using hh
  · exact hc _

lemma positiveScale_pos {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) : 0 < positiveScale t q :=
  Real.sqrt_pos.mpr (div_pos (squaredRadius_pos ht hq) hq)

lemma positiveScale_sq {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) :
    positiveScale t q ^ 2 = squaredRadius t q / q :=
  Real.sq_sqrt (div_pos (squaredRadius_pos ht hq) hq).le

lemma hasDerivAt_positiveScale_general {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) :
    HasDerivAt (positiveScale t)
      ((radialJacobian t q / positiveScale t q - positiveScale t q) / (2 * q)) q := by
  have hB := positiveScale_pos ht hq
  have hsq := positiveScale_sq ht hq
  have hh := ((hasDerivAt_squaredRadius_initial ht q).div (hasDerivAt_id q) hq.ne').sqrt
    (div_pos (squaredRadius_pos ht hq) hq).ne'
  convert hh using 1 <;> first | rfl | skip
  change (radialJacobian t q / positiveScale t q - positiveScale t q) / (2 * q) =
    (radialJacobian t q * q - squaredRadius t q * 1) / q ^ 2 / (2 * positiveScale t q)
  have hsq' : positiveScale t q ^ 2 * q = squaredRadius t q := (eq_div_iff hq.ne').mp hsq
  field_simp [hq.ne', hB.ne']
  nlinarith

lemma fderiv_blockFlow_general (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ (blockFlow omega t) z v = phase omega t *
      ((positiveScale t (‖z‖ ^ 2) : ℂ) * v +
        (((radialJacobian t (‖z‖ ^ 2) / positiveScale t (‖z‖ ^ 2) - positiveScale t (‖z‖ ^ 2)) /
          (‖z‖ ^ 2) * inner ℝ z v : ℝ) : ℂ) * z) := by
  have hq := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hs := hasDerivAt_positiveScale_general ht hq
  have hnorm := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z (hs.hasFDerivAt.comp z hnorm)
  have hh := (hc.mul_const (phase omega t)).mul (hasFDerivAt_id z)
  have he : blockFlow omega t =ᶠ[𝓝 z]
      (fun w : ℂ => (positiveScale t (‖w‖ ^ 2) : ℂ) * phase omega t * w) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact blockFlow_eq_positiveScale ht omega hw
  rw [(hh.congr_of_eventuallyEq he).fderiv]
  simp [ContinuousLinearMap.comp_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp

def tangentialFactor (t q : ℝ) : ℝ := if q = 0 then Real.exp (-2 * t) else positiveScale t q
def radialFactor (t q : ℝ) : ℝ := if q = 0 then Real.exp (-2 * t) else radialJacobian t q / positiveScale t q

lemma block_derivative_frame (omega : ℝ) {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    fderiv ℝ (blockFlow omega t) (r • a) (a * w) = (phase omega t * a) *
      ((radialFactor t (r ^ 2) * w.re : ℝ) +
        ((tangentialFactor t (r ^ 2) * w.im : ℝ) : ℂ) * Complex.I) := by
  by_cases hr₀ : r = 0
  · subst r
    simp only [zero_smul, fderiv_blockFlow_zero omega ht, radialFactor, tangentialFactor,
      zero_pow (by decide : 2 ≠ 0), if_pos rfl]
    have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by simp
    conv_lhs => rw [hw]
    push_cast
    ring
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr₀)
    have hn : ‖r • a‖ = r := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, ha, mul_one]
    have hz : r • a ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hr₀)
    have hi : inner ℝ (r • a) (a * w) = r * w.re := by rw [real_inner_smul_left, inner_unit_mul ha]
    rw [fderiv_blockFlow_general omega ht hz, hn, hi]
    simp only [radialFactor, tangentialFactor, if_neg (pow_ne_zero 2 hr₀), Complex.real_smul]
    have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by simp
    conv_lhs => rw [hw]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
    push_cast
    field_simp [show (r : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hr₀]
    ring

lemma factors_bounds {t q : ℝ} (ht : 0 ≤ t) (hq : q ∈ Icc (0 : ℝ) 2) :
    (Real.exp (-5 * t) ≤ radialFactor t q ∧ radialFactor t q ≤ Real.exp (4 * t)) ∧
    (Real.exp (-2 * t) ≤ tangentialFactor t q ∧ tangentialFactor t q ≤ Real.exp t) := by
  by_cases hzero : q = 0
  · simp only [radialFactor, tangentialFactor, if_pos hzero]
    constructor
    · constructor <;> apply Real.exp_le_exp.mpr <;> linarith
    · exact ⟨le_rfl, Real.exp_le_exp.mpr (by linarith)⟩
  · have hqp : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hzero)
    obtain ⟨hBlo, hBhi⟩ := positiveScale_bounds ht hqp hq.2
    obtain ⟨hJlo, hJhi⟩ := radialJacobian_bounds ht hq
    have hB := positiveScale_pos ht hqp
    simp only [radialFactor, tangentialFactor, if_neg hzero]
    refine ⟨⟨?_, ?_⟩, hBlo, hBhi⟩
    · apply (le_div_iff₀ hB).mpr
      calc
        Real.exp (-5 * t) * positiveScale t q ≤ Real.exp (-5 * t) * Real.exp t :=
          mul_le_mul_of_nonneg_left hBhi (Real.exp_pos _).le
        _ = Real.exp (-4 * t) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := hJlo
    · apply (div_le_iff₀ hB).mpr
      calc
        radialJacobian t q ≤ Real.exp (2 * t) := hJhi
        _ = Real.exp (4 * t) * Real.exp (-2 * t) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hBlo (Real.exp_pos _).le

lemma factors_product {t q : ℝ} (ht : 0 ≤ t) (hq : 0 ≤ q) :
    radialFactor t q * tangentialFactor t q = radialJacobian t q := by
  by_cases hz : q = 0
  · subst q
    simp [radialFactor, tangentialFactor, radialJacobian, radialDenominator, ← Real.exp_add]
    congr 1
    ring
  · simp only [radialFactor, tangentialFactor, if_neg hz]
    exact div_mul_cancel₀ _ (positiveScale_pos ht (lt_of_le_of_ne hq (Ne.symm hz))).ne'

def fullDiagonal (t q r : ℝ) : Fin 5 → ℝ :=
  ![radialFactor t q, tangentialFactor t q, radialFactor t r, tangentialFactor t r, Real.exp (-8 * t)]

lemma full_derivative_frames {t r s : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hs : 0 ≤ s)
    {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (v₀ : ℝ) (v : X) :
    fderiv ℝ (flow t) (pack (r • a) (s • b) v₀) (rotation a b v) =
      rotation (phase 1 t * a) (phase (Real.sqrt 2) t * b) (diagonalMap (fullDiagonal t (r ^ 2) (s ^ 2)) v) := by
  rw [fderiv_flow_apply ht]
  simp only [rotation, fstC_pack, sndC_pack, fifth_pack,
    block_derivative_frame 1 ht hr ha, block_derivative_frame (Real.sqrt 2) ht hs hb]
  congr 1
  · congr 1
    simp [fstC, diagonalMap_apply, fullDiagonal]
  · congr 1
    simp [sndC, diagonalMap_apply, fullDiagonal]
  · simp [diagonalMap_apply, fullDiagonal]

lemma exists_unit_direction (z : ℂ) : ∃ a : ℂ, ‖a‖ = 1 ∧ z = ‖z‖ • a := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · refine ⟨‖z‖⁻¹ • z, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
    · simp [smul_smul, norm_ne_zero_iff.mpr hz]

lemma flow_gram_charpoly {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ((fderiv ℝ (flow t) x).toLinearMap.adjoint.comp (fderiv ℝ (flow t) x).toLinearMap).charpoly =
      ∏ i : Fin 5, (Polynomial.X - Polynomial.C (fullDiagonal t (q₁ x) (q₂ x) i ^ 2)) := by
  obtain ⟨a, ha, hza⟩ := exists_unit_direction (fstC x)
  obtain ⟨b, hb, hzb⟩ := exists_unit_direction (sndC x)
  have hc : ‖phase 1 t * a‖ = 1 := by rw [norm_mul, norm_phase, ha, mul_one]
  have hd : ‖phase (Real.sqrt 2) t * b‖ = 1 := by rw [norm_mul, norm_phase, hb, mul_one]
  apply gram_charpoly_of_frames _ (rotationIsometry a b ha hb)
    (rotationIsometry (phase 1 t * a) (phase (Real.sqrt 2) t * b) hc hd)
  intro v
  have hh := full_derivative_frames ht (norm_nonneg (fstC x)) (norm_nonneg (sndC x)) ha hb (x 4) v
  rwa [← hza, ← hzb, pack_coordinates, norm_fstC_sq, norm_sndC_sq] at hh

lemma fullDiagonal_bounds {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) (i : Fin 5) :
    Real.exp (-8 * t) ≤ fullDiagonal t (q₁ x) (q₂ x) i ∧
      fullDiagonal t (q₁ x) (q₂ x) i ≤ Real.exp (4 * t) := by
  have h₁ := factors_bounds ht (show q₁ x ∈ Icc (0 : ℝ) 2 from ⟨q₁_nonneg x, hx.1⟩)
  have h₂ := factors_bounds ht (show q₂ x ∈ Icc (0 : ℝ) 2 from ⟨q₂_nonneg x, hx.2.1⟩)
  have h85 : Real.exp (-8 * t) ≤ Real.exp (-5 * t) := Real.exp_le_exp.mpr (by linarith)
  have h82 : Real.exp (-8 * t) ≤ Real.exp (-2 * t) := Real.exp_le_exp.mpr (by linarith)
  have h14 : Real.exp t ≤ Real.exp (4 * t) := Real.exp_le_exp.mpr (by linarith)
  fin_cases i <;> simp only [fullDiagonal, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact ⟨h85.trans h₁.1.1, h₁.1.2⟩
  · exact ⟨h82.trans h₁.2.1, h₁.2.2.trans h14⟩
  · exact ⟨h85.trans h₂.1.1, h₂.1.2⟩
  · exact ⟨h82.trans h₂.2.1, h₂.2.2.trans h14⟩
  · exact ⟨le_rfl, Real.exp_le_exp.mpr (by linarith)⟩

lemma flow_singularValues_decreasing {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) (i : Fin 5) :
    system.σ t x i = decreasingValues (fullDiagonal t (q₁ x) (q₂ x)) i := by
  exact singularValues_eq_decreasing (fderiv ℝ (flow t) x).toLinearMap _
    (fun j => (Real.exp_pos _).le.trans (fullDiagonal_bounds ht hx j).1) (flow_gram_charpoly ht x) i

lemma flow_singularValues_bounds {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) (i : Fin 5) :
    Real.exp (-8 * t) ≤ system.σ t x i ∧ system.σ t x i ≤ Real.exp (4 * t) := by
  rw [flow_singularValues_decreasing ht hx]
  exact fullDiagonal_bounds ht hx _

lemma flow_fifth_singularValue {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) :
    system.σ t x 4 = Real.exp (-8 * t) := by
  rw [flow_singularValues_decreasing ht hx (⟨4, by decide⟩ : Fin 5)]
  exact decreasingValues_last _ (fun i => (fullDiagonal_bounds ht hx i).1)

lemma flow_singularValues_product {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) :
    (∏ i : Fin 5, system.σ t x i) = radialJacobian t (q₁ x) * radialJacobian t (q₂ x) * Real.exp (-8 * t) := by
  simp_rw [flow_singularValues_decreasing ht hx]
  rw [prod_decreasingValues]
  simp only [fullDiagonal, Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
  rw [← factors_product ht (q₁_nonneg x), ← factors_product ht (q₂_nonneg x)]
  ring

end Eden.PolynomialCounterexample
