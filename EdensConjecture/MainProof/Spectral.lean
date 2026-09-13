import EdensConjecture.MainProof.Flow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate

namespace Eden
namespace PolynomialCounterexample

lemma kaplanYorkeIndex_le (n : ℕ) (rates : ℕ → ℝ) : kaplanYorkeIndex n rates ≤ n := by
  apply csSup_le
  · exact ⟨0, Nat.zero_le _, by simp [exponentSum]⟩
  · exact fun j hj => hj.1

lemma kaplanYorkeIndex_mem (n : ℕ) (rates : ℕ → ℝ) :
    0 ≤ exponentSum rates (kaplanYorkeIndex n rates) := by
  have hne : ({j : ℕ | j ≤ n ∧ 0 ≤ exponentSum rates j} : Set ℕ).Nonempty :=
    ⟨0, Nat.zero_le _, by simp [exponentSum]⟩
  have hb : BddAbove {j : ℕ | j ≤ n ∧ 0 ≤ exponentSum rates j} := ⟨n, fun j hj => hj.1⟩
  exact (Nat.sSup_mem hne hb).2

lemma kaplanYorkeDimension_le (n : ℕ) (rates : ℕ → ℝ) : kaplanYorkeDimension n rates ≤ n := by
  let j := kaplanYorkeIndex n rates
  have hj : j ≤ n := kaplanYorkeIndex_le n rates
  have hs : 0 ≤ exponentSum rates j := kaplanYorkeIndex_mem n rates
  unfold kaplanYorkeDimension
  change (if j = n then (n : ℝ) else (j : ℝ) + exponentSum rates j / |rates j|) ≤ n
  split_ifs with heq
  · rfl
  · have hjn : j < n := lt_of_le_of_ne hj heq
    have hnext : exponentSum rates (j + 1) < 0 := by
      by_contra hh
      have hm : j + 1 ∈ {k : ℕ | k ≤ n ∧ 0 ≤ exponentSum rates k} :=
        ⟨hjn, le_of_not_gt hh⟩
      have hle : j + 1 ≤ j := le_csSup ⟨n, fun k hk => hk.1⟩ hm
      omega
    have hsum : exponentSum rates (j + 1) = exponentSum rates j + rates j := by
      simp [exponentSum, Finset.sum_range_succ]
    rw [hsum] at hnext
    have hr : rates j < 0 := by linarith
    have hquot : exponentSum rates j / |rates j| < 1 := by
      rw [abs_of_neg hr, div_lt_one (by linarith)]
      linarith
    have hcast : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
    linarith

lemma finiteTimeLyapunovDimension_le {n : ℕ} (D : C1DynamicalSystem n)
    (A : Set (PhaseSpace n)) (hA : A.Nonempty) (t : ℝ) :
    finiteTimeLyapunovDimension D t A ≤ n := by
  apply csSup_le (hA.image _)
  rintro d ⟨x, _, rfl⟩
  exact kaplanYorkeDimension_le n (D.finiteTimeLE t x)

lemma local_dimension_eq_of_constant_rates {n : ℕ} (D : C1DynamicalSystem n)
    (x : PhaseSpace n) (rates : ℕ → ℝ)
    (hc : ∀ t : ℝ, 0 < t → D.finiteTimeLE t x = rates) :
    localLyapunovDimension D x = kaplanYorkeDimension n rates := by
  have he : (fun t : ℝ => finiteTimeLocalLyapunovDimension D t x)
      =ᶠ[atTop] (fun _ => kaplanYorkeDimension n rates) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [finiteTimeLocalLyapunovDimension, hc t ht]
  exact (tendsto_const_nhds.congr' he.symm).liminf_eq

lemma singularValues_eq_of_charpoly {n : ℕ} (A : PhaseSpace n →ₗ[ℝ] PhaseSpace n)
    (values : Fin n → ℝ) (hpos : ∀ i, 0 ≤ values i) (hsort : Antitone values)
    (hchar : (A.adjoint ∘ₗ A).charpoly =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (values i ^ 2))) (i : Fin n) :
    A.singularValues i = values i := by
  have hn : Module.finrank ℝ (PhaseSpace n) = n := by simp [PhaseSpace]
  have hroots : (A.adjoint ∘ₗ A).charpoly.roots =
      (Finset.univ.val.map (fun j : Fin n => values j ^ 2)) := by
    rw [hchar, Polynomial.roots_prod _ _ (by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact Polynomial.X_sub_C_ne_zero (values j ^ 2))]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  have heigen := A.isSymmetric_adjoint_comp_self.sort_roots_charpoly_eq_eigenvalues hn
  rw [hroots] at heigen
  have hsortsq : Antitone (fun j : Fin n => values j ^ 2) := by
    intro j k hjk
    exact (sq_le_sq₀ (hpos k) (hpos j)).mpr (hsort hjk)
  have hlist : ((Finset.univ.val.map (fun j : Fin n => values j ^ 2)).map RCLike.re).sort (· ≥ ·) =
      List.ofFn (fun j : Fin n => values j ^ 2) := by
    simp only [Multiset.map_map, Function.comp_def, RCLike.re_to_real]
    rw [Fin.univ_val_map, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hsortsq.sortedGE_ofFn
  rw [hlist] at heigen
  have heq := List.ofFn_inj.mp heigen
  rw [A.singularValues_fin hn, ← congrFun heq i, Real.sqrt_sq (hpos i)]

def positiveScale (t q : ℝ) : ℝ := Real.sqrt (squaredRadius t q / q)

lemma blockFlow_eq_positiveScale {t : ℝ} (ht : 0 ≤ t) (omega : ℝ) {z : ℂ} (hz : z ≠ 0) :
    blockFlow omega t z = (positiveScale t (‖z‖ ^ 2) : ℂ) * phase omega t * z := by
  have hn := norm_pos_iff.mpr hz
  have hq := squaredRadius_nonneg ht (sq_nonneg ‖z‖)
  have heq : positiveScale t (‖z‖ ^ 2) = radius t ‖z‖ / ‖z‖ := by
    rw [positiveScale, Real.sqrt_div hq, Real.sqrt_sq hn.le]
    rfl
  rw [heq]
  rfl

lemma hasDerivAt_positiveScale_fixed {t q L : ℝ} (hq : 0 < q)
    (hfix : squaredRadius t q = q) (hder : HasDerivAt (squaredRadius t) L q) :
    HasDerivAt (positiveScale t) ((L - 1) / (2 * q)) q := by
  have hh := (hder.div (hasDerivAt_id q) hq.ne').sqrt
    (by change squaredRadius t q / q ≠ 0; rw [hfix, div_self hq.ne']; norm_num)
  convert hh using 1 <;> first | rfl | skip
  change (L - 1) / (2 * q) = (L * q - squaredRadius t q * 1) / q ^ 2 /
    (2 * Real.sqrt (squaredRadius t q / q))
  rw [hfix, div_self hq.ne']
  norm_num
  field_simp

lemma positiveScale_fixed {t q : ℝ} (hq : q ≠ 0) (hfix : squaredRadius t q = q) :
    positiveScale t q = 1 := by simp [positiveScale, hfix, hq]

lemma fderiv_blockFlow_fixed (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ≠ 0) {L : ℝ} (hfix : squaredRadius t (‖z‖ ^ 2) = ‖z‖ ^ 2)
    (hder : HasDerivAt (squaredRadius t) L (‖z‖ ^ 2)) (v : ℂ) :
    fderiv ℝ (blockFlow omega t) z v =
      phase omega t * (v + (((L - 1) / (‖z‖ ^ 2) * inner ℝ z v : ℝ) : ℂ) * z) := by
  have hq := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hs := hasDerivAt_positiveScale_fixed hq hfix hder
  have hnorm := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z (hs.hasFDerivAt.comp z hnorm)
  have hh := ((hc.mul_const (phase omega t)).mul (hasFDerivAt_id z))
  have he : blockFlow omega t =ᶠ[𝓝 z]
      (fun w : ℂ => (positiveScale t (‖w‖ ^ 2) : ℂ) * phase omega t * w) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact blockFlow_eq_positiveScale ht omega hw
  have hd := hh.congr_of_eventuallyEq he
  rw [hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, positiveScale_fixed hq.ne' hfix,
    Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp

lemma sqrt_exp_double (a : ℝ) : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
  rw [show 2 * a = a + a by ring, Real.exp_add, ← pow_two, Real.sqrt_sq (Real.exp_pos a).le]

lemma hasDerivAt_squaredRadius_one {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (squaredRadius t) (Real.exp (2 * t)) 1 := by
  have hh := hasDerivAt_squaredRadius_initial ht 1
  have hroot : Real.sqrt (Real.exp (-4 * t)) = Real.exp (-2 * t) := by
    rw [show -4 * t = 2 * (-2 * t) by ring, sqrt_exp_double]
  convert hh using 1
  simp only [radialDenominator, sub_self, zero_pow (by decide : 2 ≠ 0),
    sub_zero, one_mul, zero_add, hroot]
  rw [← Real.exp_nat_mul, ← Real.exp_sub]
  congr 1
  ring

lemma hasDerivAt_squaredRadius_two {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (squaredRadius t) (Real.exp (-4 * t)) 2 := by
  have hh := hasDerivAt_squaredRadius_initial ht 2
  convert hh using 1 <;> norm_num [radialDenominator]

lemma fderiv_blockFlow_one (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : ‖z‖ = 1) (v : ℂ) :
    fderiv ℝ (blockFlow omega t) z v =
      phase omega t * (v + (((Real.exp (2 * t) - 1) * inner ℝ z v : ℝ) : ℂ) * z) := by
  have hn : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have hs : ‖z‖ ^ 2 = 1 := by rw [hz]; norm_num
  have hfix : squaredRadius t (‖z‖ ^ 2) = ‖z‖ ^ 2 := by rw [hs, squaredRadius_at_one]
  have hd : HasDerivAt (squaredRadius t) (Real.exp (2 * t)) (‖z‖ ^ 2) := by
    rw [hs]
    exact hasDerivAt_squaredRadius_one ht
  simpa only [hs, div_one] using fderiv_blockFlow_fixed omega ht hn hfix hd v

lemma fderiv_blockFlow_two (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : ‖z‖ ^ 2 = 2) (v : ℂ) :
    fderiv ℝ (blockFlow omega t) z v =
      phase omega t * (v + (((Real.exp (-4 * t) - 1) / 2 * inner ℝ z v : ℝ) : ℂ) * z) := by
  have hn : z ≠ 0 := by intro hh; simp [hh] at hz
  have hfix : squaredRadius t (‖z‖ ^ 2) = ‖z‖ ^ 2 := by rw [hz, squaredRadius_at_two]
  have hd : HasDerivAt (squaredRadius t) (Real.exp (-4 * t)) (‖z‖ ^ 2) := by
    rw [hz]
    exact hasDerivAt_squaredRadius_two ht
  simpa only [hz] using fderiv_blockFlow_fixed omega ht hn hfix hd v

lemma fderiv_blockFlow_zero (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) (v : ℂ) :
    fderiv ℝ (blockFlow omega t) 0 v = (Real.exp (-2 * t) : ℂ) * phase omega t * v := by
  have hs := (contDiffAt_regularScaleSq ht (by norm_num : (0 : ℝ) < 1)).sqrt
    (regularScaleSq_pos ht (by norm_num : (0 : ℝ) < 1)).ne'
  have hsq : ContDiffAt ℝ ⊤ (fun w : ℂ => ‖w‖ ^ 2) 0 := (contDiff_norm_sq ℂ).contDiffAt
  have hs' : ContDiffAt ℝ ⊤ (fun q => Real.sqrt (regularScaleSq t q)) (‖(0 : ℂ)‖ ^ 2) := by
    simpa using hs
  have hcomp := hs'.comp (0 : ℂ) hsq
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ) hcomp
  have hd := hc.differentiableAt (by simp)
  have hh := (hd.hasFDerivAt.mul_const (phase omega t)).mul (hasFDerivAt_id (0 : ℂ))
  have he : blockFlow omega t =ᶠ[𝓝 (0 : ℂ)]
      (fun w => (Real.sqrt (regularScaleSq t (‖w‖ ^ 2)) : ℂ) * phase omega t * w) := by
    have he' : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ ^ 2 < 1 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by norm_num)
    filter_upwards [he'] with w hw
    exact blockFlow_eq_regular ht omega hw
  rw [(hh.congr_of_eventuallyEq he).fderiv]
  have hroot : Real.sqrt (Real.exp (-4 * t)) = Real.exp (-2 * t) := by
    rw [show -4 * t = 2 * (-2 * t) by ring, sqrt_exp_double]
  have hscale : Real.sqrt (regularScaleSq t (‖(0 : ℂ)‖ ^ 2)) = Real.exp (-2 * t) := by
    have heq : regularScaleSq t (‖(0 : ℂ)‖ ^ 2) = Real.exp (-4 * t) := by
      norm_num [regularScaleSq, radialDenominator]
    rw [heq, hroot]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Function.comp_apply, Complex.ofRealCLM_apply,
    id_eq, zero_smul, zero_add, add_zero, hscale, smul_eq_mul]

def fstCLM : X →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
  { toFun := fstC
    map_add' := by intros; simp [fstC]; ring
    map_smul' := by intros; simp [fstC, Complex.real_smul]; ring }

def sndCLM : X →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
  { toFun := sndC
    map_add' := by intros; simp [sndC]; ring
    map_smul' := by intros; simp [sndC, Complex.real_smul]; ring }

def fifthCLM : X →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun x => x 4
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

def packCLM : (ℂ × ℂ × ℝ) →L[ℝ] X := LinearMap.toContinuousLinearMap
  { toFun := fun p => pack p.1 p.2.1 p.2.2
    map_add' := by
      intro p q
      ext i
      fin_cases i <;> simp [pack]
    map_smul' := by
      intro a p
      ext i
      fin_cases i <;> simp [pack, Complex.real_smul] }

lemma fderiv_flow_apply {t : ℝ} (ht : 0 ≤ t) (x v : X) :
    fderiv ℝ (flow t) x v =
      pack (fderiv ℝ (blockFlow 1 t) (fstC x) (fstC v))
        (fderiv ℝ (blockFlow (Real.sqrt 2) t) (sndC x) (sndC v))
        (Real.exp (-8 * t) * v 4) := by
  have h₁ := ((contDiff_blockFlow 1 ht).differentiable (by simp) (fstC x)).hasFDerivAt.comp x
    fstCLM.hasFDerivAt
  have h₂ := ((contDiff_blockFlow (Real.sqrt 2) ht).differentiable (by simp) (sndC x)).hasFDerivAt.comp x
    sndCLM.hasFDerivAt
  have hv := (fifthCLM.hasFDerivAt (x := x)).const_mul (Real.exp (-8 * t))
  have hh := packCLM.hasFDerivAt.comp x (h₁.prodMk (h₂.prodMk hv))
  change HasFDerivAt (flow t) _ x at hh
  rw [hh.fderiv]
  rfl

def rotation (a b : ℂ) (x : X) : X := pack (a * fstC x) (b * sndC x) (x 4)

lemma rotation_add (a b : ℂ) (x y : X) : rotation a b (x + y) = rotation a b x + rotation a b y := by
  ext i
  fin_cases i <;> simp [rotation, pack, fstC, sndC] <;> ring

lemma rotation_smul (a b : ℂ) (c : ℝ) (x : X) : rotation a b (c • x) = c • rotation a b x := by
  ext i
  fin_cases i <;> simp [rotation, pack, fstC, sndC, Complex.real_smul] <;> ring

lemma rotation_comp (a b c d : ℂ) (x : X) :
    rotation a b (rotation c d x) = rotation (a * c) (b * d) x := by
  simp [rotation, mul_assoc]

lemma rotation_one (x : X) : rotation 1 1 x = x := by simp [rotation]

lemma norm_rotation {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (x : X) :
    ‖rotation a b x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [rotation, norm_pack_sq, norm_mul, norm_mul, ha, hb, one_mul, one_mul,
    norm_fstC_sq, norm_sndC_sq, norm_sq]

def rotationIsometry (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : X ≃ₗᵢ[ℝ] X where
  toFun := rotation a b
  invFun := rotation (star a) (star b)
  map_add' := rotation_add a b
  map_smul' := rotation_smul a b
  left_inv := by
    intro x
    rw [rotation_comp]
    have ha' : star a * a = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, ← Complex.sq_norm, ha]
      norm_num
    have hb' : star b * b = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, ← Complex.sq_norm, hb]
      norm_num
    rw [ha', hb', rotation_one]
  right_inv := by
    intro x
    rw [rotation_comp]
    have ha' : a * star a = 1 := by
      rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, ha]
      norm_num
    have hb' : b * star b = 1 := by
      rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm, hb]
      norm_num
    rw [ha', hb', rotation_one]
  norm_map' := norm_rotation ha hb

def diagonalMap (c : Fin 5 → ℝ) : X →ₗ[ℝ] X :=
  Matrix.toEuclideanLin (Matrix.diagonal c)

lemma diagonalMap_apply (c : Fin 5 → ℝ) (x : X) (i : Fin 5) :
    diagonalMap c x i = c i * x i := by
  simp [diagonalMap, Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal]

lemma diagonalMap_charpoly (c : Fin 5 → ℝ) :
    (diagonalMap c).charpoly = ∏ i, (Polynomial.X - Polynomial.C (c i)) := by
  rw [← LinearMap.charpoly_toMatrix _ (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis]
  change (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
    (Matrix.toLin (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis (Matrix.diagonal c))).charpoly = _
  rw [LinearMap.toMatrix_toLin, Matrix.charpoly_diagonal]

lemma inner_diagonalMap (c : Fin 5 → ℝ) (x y : X) :
    inner ℝ (diagonalMap c x) (diagonalMap c y) =
      inner ℝ (diagonalMap (fun i => c i ^ 2) x) y := by
  simp only [PiLp.inner_apply, Real.inner_apply, diagonalMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma gram_charpoly_of_frames (A : X →ₗ[ℝ] X) (U V : X ≃ₗᵢ[ℝ] X) (c : Fin 5 → ℝ)
    (hA : ∀ x : X, A (U x) = V (diagonalMap c x)) :
    (A.adjoint ∘ₗ A).charpoly = ∏ i, (Polynomial.X - Polynomial.C (c i ^ 2)) := by
  have heq : U.toLinearEquiv.symm.conj (A.adjoint ∘ₗ A) = diagonalMap (fun i => c i ^ 2) := by
    apply LinearMap.ext
    intro x
    apply U.injective
    simp only [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearIsometryEquiv.coe_toLinearEquiv,
       LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply]
    change U (U.symm (A.adjoint (A (U x)))) = U (diagonalMap (fun i => c i ^ 2) x)
    rw [U.apply_symm_apply]
    apply ext_inner_right ℝ
    intro y
    obtain ⟨z, rfl⟩ := U.surjective y
    rw [LinearMap.adjoint_inner_left, hA, hA, U.inner_map_map, V.inner_map_map,
      inner_diagonalMap]
  rw [← U.toLinearEquiv.symm.charpoly_conj (A.adjoint ∘ₗ A), heq, diagonalMap_charpoly]

lemma inner_unit_mul {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) : inner ℝ a (a * w) = w.re := by
  rw [Complex.inner, show a * w * starRingEnd ℂ a = (a * starRingEnd ℂ a) * w by ring,
    Complex.mul_conj, ← Complex.sq_norm, ha]
  simp

lemma fderiv_blockFlow_one_frame (omega : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    fderiv ℝ (blockFlow omega t) a (a * w) =
      (phase omega t * a) * ((Real.exp (2 * t) * w.re : ℝ) + (w.im : ℂ) * Complex.I) := by
  rw [fderiv_blockFlow_one omega ht ha, inner_unit_mul ha]
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by simp
  rw [hw]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
  push_cast
  ring

lemma fderiv_blockFlow_two_frame (omega : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    fderiv ℝ (blockFlow omega t) ((Real.sqrt 2 : ℝ) • a) (a * w) =
      (phase omega t * a) * ((Real.exp (-4 * t) * w.re : ℝ) + (w.im : ℂ) * Complex.I) := by
  have hn : ‖(Real.sqrt 2 : ℝ) • a‖ ^ 2 = 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), ha, mul_one,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [fderiv_blockFlow_two omega ht hn, real_inner_smul_left, inner_unit_mul ha]
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by simp
  rw [hw]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
  simp only [Complex.real_smul]
  push_cast
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  linear_combination (phase omega t * a * (Complex.exp (-4 * (t : ℂ)) - 1) * (w.re : ℂ) / 2) * hs

lemma fderiv_blockFlow_zero_frame (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) (w : ℂ) :
    fderiv ℝ (blockFlow omega t) 0 w =
      phase omega t * ((Real.exp (-2 * t) * w.re : ℝ) +
        ((Real.exp (-2 * t) * w.im : ℝ) : ℂ) * Complex.I) := by
  rw [fderiv_blockFlow_zero omega ht]
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by simp
  rw [hw]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
  push_cast
  ring

def torusDiagonal (t : ℝ) : Fin 5 → ℝ :=
  ![Real.exp (2 * t), 1, Real.exp (2 * t), 1, Real.exp (-8 * t)]

def torusSingularValues (t : ℝ) : Fin 5 → ℝ :=
  ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-8 * t)]

lemma torus_derivative_frames {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ T) (v : X) :
    fderiv ℝ (flow t) x (rotation (fstC x) (sndC x) v) =
      rotation (phase 1 t * fstC x) (phase (Real.sqrt 2) t * sndC x) (diagonalMap (torusDiagonal t) v) := by
  have ha : ‖fstC x‖ = 1 := by
    have hh := norm_fstC_sq x
    rw [hx.1] at hh
    nlinarith [norm_nonneg (fstC x)]
  have hb : ‖sndC x‖ = 1 := by
    have hh := norm_sndC_sq x
    rw [hx.2.1] at hh
    nlinarith [norm_nonneg (sndC x)]
  rw [fderiv_flow_apply ht]
  simp only [rotation, fstC_pack, sndC_pack, fifth_pack,
    fderiv_blockFlow_one_frame 1 ht ha, fderiv_blockFlow_one_frame (Real.sqrt 2) ht hb]
  congr 1
  · congr 1
    simp [fstC, diagonalMap_apply, torusDiagonal]
  · congr 1
    simp [sndC, diagonalMap_apply, torusDiagonal]
  · simp [diagonalMap_apply, torusDiagonal]

lemma torus_gram_charpoly {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ T) :
    ((fderiv ℝ (flow t) x).toLinearMap.adjoint ∘ₗ (fderiv ℝ (flow t) x).toLinearMap).charpoly =
      ∏ i : Fin 5, (Polynomial.X - Polynomial.C (torusSingularValues t i ^ 2)) := by
  have ha : ‖fstC x‖ = 1 := by
    have hh := norm_fstC_sq x
    rw [hx.1] at hh
    nlinarith [norm_nonneg (fstC x)]
  have hb : ‖sndC x‖ = 1 := by
    have hh := norm_sndC_sq x
    rw [hx.2.1] at hh
    nlinarith [norm_nonneg (sndC x)]
  have hc : ‖phase 1 t * fstC x‖ = 1 := by rw [norm_mul, norm_phase, ha, mul_one]
  have hd : ‖phase (Real.sqrt 2) t * sndC x‖ = 1 := by rw [norm_mul, norm_phase, hb, mul_one]
  have hh := gram_charpoly_of_frames (fderiv ℝ (flow t) x).toLinearMap
    (rotationIsometry (fstC x) (sndC x) ha hb)
    (rotationIsometry (phase 1 t * fstC x) (phase (Real.sqrt 2) t * sndC x) hc hd)
    (torusDiagonal t) (torus_derivative_frames ht hx)
  rw [hh]
  simp [torusDiagonal, torusSingularValues, Fin.prod_univ_succ]
  ring_nf
  simp

lemma torus_singularValues {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ T) (i : Fin 5) :
    system.σ t x i = torusSingularValues t i := by
  apply singularValues_eq_of_charpoly (fderiv ℝ (flow t) x).toLinearMap
    (torusSingularValues t) _ _ (torus_gram_charpoly ht hx)
  · intro j
    fin_cases j <;> simp [torusSingularValues] <;> positivity
  · have hbig : 1 ≤ Real.exp (2 * t) := Real.one_le_exp_iff.mpr (by linarith)
    have hsmall : Real.exp (-8 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    apply Fin.antitone_iff_succ_le.mpr
    intro j
    fin_cases j <;> simp [torusSingularValues] <;> assumption

lemma upperLE_eq_of_finiteTimeLE {n : ℕ} (D : C1DynamicalSystem n) (x : PhaseSpace n)
    (i : ℕ) (c : ℝ) (hc : ∀ t : ℝ, 0 < t → D.finiteTimeLE t x i = c) :
    D.upperLE x i = c := by
  have he : (fun t : ℝ => D.finiteTimeLE t x i) =ᶠ[atTop] (fun _ => c) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact hc t ht
  exact (tendsto_const_nhds.congr' he.symm).limsup_eq

lemma torus_finiteTimeLE {t : ℝ} (ht : 0 < t) {x : X} (hx : x ∈ T) (i : Fin 5) :
    system.finiteTimeLE t x i = spectrum 2 2 0 0 (-8) i := by
  unfold C1DynamicalSystem.finiteTimeLE
  rw [torus_singularValues ht.le hx]
  fin_cases i <;> simp [torusSingularValues, spectrum, ht.ne', Real.log_exp] <;> field_simp

lemma torus_upperLE {x : X} (hx : x ∈ T) : system.upperLE x = spectrum 2 2 0 0 (-8) := by
  funext i
  by_cases hi : i < 5
  · exact upperLE_eq_of_finiteTimeLE system x i _ (fun t ht => torus_finiteTimeLE ht hx ⟨i, hi⟩)
  · apply upperLE_eq_of_finiteTimeLE
    intro t ht
    have hs : system.σ t x i = 0 := by
      apply LinearMap.singularValues_of_finrank_le
      simpa [PhaseSpace] using le_of_not_gt hi
    rw [C1DynamicalSystem.finiteTimeLE, hs]
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h4 : i ≠ 4 := by omega
    simp [spectrum, h0, h1, h2, h3, h4]

lemma torus_finiteTimeLE_all {t : ℝ} (ht : 0 < t) {x : X} (hx : x ∈ T) : system.finiteTimeLE t x = spectrum 2 2 0 0 (-8) := by
  funext i
  by_cases hi : i < 5
  · exact torus_finiteTimeLE ht hx ⟨i, hi⟩
  · have hs : system.σ t x i = 0 := by
      apply LinearMap.singularValues_of_finrank_le
      simpa [PhaseSpace] using le_of_not_gt hi
    rw [C1DynamicalSystem.finiteTimeLE, hs]
    have h0 : i ≠ 0 := by omega
    have h1 : i ≠ 1 := by omega
    have h2 : i ≠ 2 := by omega
    have h3 : i ≠ 3 := by omega
    have h4 : i ≠ 4 := by omega
    simp [spectrum, h0, h1, h2, h3, h4]

lemma torus_localLyapunovDimension {x : X} (hx : x ∈ T) :
    localLyapunovDimension system x = 9 / 2 := by
  rw [local_dimension_eq_of_constant_rates system x _ (fun t ht => torus_finiteTimeLE_all ht hx),
    spectrum_BB_dimension]

inductive RadialType where
  | zero | one | two
  deriving DecidableEq

def RadialType.point : RadialType → ℂ → ℂ
  | .zero, _ => 0
  | .one, a => a
  | .two, a => (Real.sqrt 2 : ℝ) • a

def RadialType.radialRate : RadialType → ℝ
  | .zero => -2
  | .one => 2
  | .two => -4

def RadialType.tangentialRate : RadialType → ℝ
  | .zero => -2
  | .one => 0
  | .two => 0

lemma RadialType.derivative_frame (r : RadialType) (omega : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {a : ℂ} (ha : ‖a‖ = 1) (w : ℂ) :
    fderiv ℝ (blockFlow omega t) (r.point a) (a * w) =
      (phase omega t * a) *
        ((Real.exp (r.radialRate * t) * w.re : ℝ) +
          ((Real.exp (r.tangentialRate * t) * w.im : ℝ) : ℂ) * Complex.I) := by
  cases r
  · rw [RadialType.point, fderiv_blockFlow_zero omega ht]
    have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by simp
    rw [hw]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, sub_zero]
    simp only [RadialType.radialRate, RadialType.tangentialRate]
    push_cast
    ring
  · simpa [RadialType.point, RadialType.radialRate, RadialType.tangentialRate] using
      fderiv_blockFlow_one_frame omega ht ha w
  · simpa [RadialType.point, RadialType.radialRate, RadialType.tangentialRate] using
      fderiv_blockFlow_two_frame omega ht ha w

def equilibriumDiagonal (r s : RadialType) (t : ℝ) : Fin 5 → ℝ :=
  ![Real.exp (r.radialRate * t), Real.exp (r.tangentialRate * t),
    Real.exp (s.radialRate * t), Real.exp (s.tangentialRate * t), Real.exp (-8 * t)]

lemma equilibrium_derivative_frames (r s : RadialType) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (v : X) :
    fderiv ℝ (flow t) (pack (r.point a) (s.point b) 0) (rotation a b v) =
      rotation (phase 1 t * a) (phase (Real.sqrt 2) t * b) (diagonalMap (equilibriumDiagonal r s t) v) := by
  rw [fderiv_flow_apply ht]
  simp only [rotation, fstC_pack, sndC_pack, fifth_pack,
    r.derivative_frame 1 ht ha, s.derivative_frame (Real.sqrt 2) ht hb]
  congr 1
  · congr 1
    simp [fstC, diagonalMap_apply, equilibriumDiagonal]
  · congr 1
    simp [sndC, diagonalMap_apply, equilibriumDiagonal]
  · simp [diagonalMap_apply, equilibriumDiagonal]

lemma equilibrium_gram_charpoly (r s : RadialType) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    ((fderiv ℝ (flow t) (pack (r.point a) (s.point b) 0)).toLinearMap.adjoint ∘ₗ
      (fderiv ℝ (flow t) (pack (r.point a) (s.point b) 0)).toLinearMap).charpoly =
      ∏ i : Fin 5, (Polynomial.X - Polynomial.C (equilibriumDiagonal r s t i ^ 2)) := by
  have hc : ‖phase 1 t * a‖ = 1 := by rw [norm_mul, norm_phase, ha, mul_one]
  have hd : ‖phase (Real.sqrt 2) t * b‖ = 1 := by rw [norm_mul, norm_phase, hb, mul_one]
  exact gram_charpoly_of_frames _ (rotationIsometry a b ha hb)
    (rotationIsometry (phase 1 t * a) (phase (Real.sqrt 2) t * b) hc hd)
    (equilibriumDiagonal r s t) (equilibrium_derivative_frames r s ha hb ht)

def radialPairSpectrum : RadialType → RadialType → SpectrumType
  | .zero, .zero => .AA
  | .zero, .one | .one, .zero => .AB
  | .zero, .two | .two, .zero => .AC
  | .one, .one => .BB
  | .one, .two | .two, .one => .BC
  | .two, .two => .CC

lemma SpectrumType.rates_antitone_fin (s : SpectrumType) :
    Antitone (fun i : Fin 5 => s.rates i) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  cases s <;> fin_cases i <;> norm_num [SpectrumType.rates, spectrum]

lemma equilibrium_singularValues (r s : RadialType) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin 5) :
    system.σ t (pack (r.point a) (s.point b) 0) i =
      Real.exp ((radialPairSpectrum r s).rates i * t) := by
  apply singularValues_eq_of_charpoly _ (fun j => Real.exp ((radialPairSpectrum r s).rates j * t))
  · intro j
    exact (Real.exp_pos _).le
  · intro j k hjk
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      ((radialPairSpectrum r s).rates_antitone_fin hjk) ht)
  · change ((fderiv ℝ (flow t) (pack (r.point a) (s.point b) 0)).toLinearMap.adjoint ∘ₗ
      (fderiv ℝ (flow t) (pack (r.point a) (s.point b) 0)).toLinearMap).charpoly = _
    rw [equilibrium_gram_charpoly r s ha hb ht]
    cases r <;> cases s <;>
      simp [equilibriumDiagonal, radialPairSpectrum, SpectrumType.rates, spectrum,
        RadialType.radialRate, RadialType.tangentialRate, Fin.prod_univ_succ] <;> ring_nf <;> simp

lemma SpectrumType.rates_eq_zero_of_ge_five (s : SpectrumType) {i : ℕ} (hi : 5 ≤ i) : s.rates i = 0 := by
  have h0 : i ≠ 0 := by omega
  have h1 : i ≠ 1 := by omega
  have h2 : i ≠ 2 := by omega
  have h3 : i ≠ 3 := by omega
  have h4 : i ≠ 4 := by omega
  cases s <;> simp [SpectrumType.rates, spectrum, h0, h1, h2, h3, h4]

lemma equilibrium_upperLE (r s : RadialType) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    system.upperLE (pack (r.point a) (s.point b) 0) = (radialPairSpectrum r s).rates := by
  funext i
  apply upperLE_eq_of_finiteTimeLE
  intro t ht
  unfold C1DynamicalSystem.finiteTimeLE
  by_cases hi : i < 5
  · rw [equilibrium_singularValues r s ha hb ht.le ⟨i, hi⟩, Real.log_exp,
      mul_div_cancel_right₀ _ ht.ne']
  · have hsigma : system.σ t (pack (r.point a) (s.point b) 0) i = 0 := by
      apply LinearMap.singularValues_of_finrank_le
      simpa [PhaseSpace] using le_of_not_gt hi
    rw [hsigma, (radialPairSpectrum r s).rates_eq_zero_of_ge_five (le_of_not_gt hi)]
    simp

lemma equilibrium_finiteTimeLE_all (r s : RadialType) {t : ℝ} (ht : 0 < t) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    system.finiteTimeLE t (pack (r.point a) (s.point b) 0) = (radialPairSpectrum r s).rates := by
  funext i
  unfold C1DynamicalSystem.finiteTimeLE
  by_cases hi : i < 5
  · rw [equilibrium_singularValues r s ha hb ht.le ⟨i, hi⟩, Real.log_exp,
      mul_div_cancel_right₀ _ ht.ne']
  · have hsigma : system.σ t (pack (r.point a) (s.point b) 0) i = 0 := by
      apply LinearMap.singularValues_of_finrank_le
      simpa [PhaseSpace] using le_of_not_gt hi
    rw [hsigma, (radialPairSpectrum r s).rates_eq_zero_of_ge_five (le_of_not_gt hi)]
    simp

lemma equilibrium_local_dimension (r s : RadialType) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    localLyapunovDimension system (pack (r.point a) (s.point b) 0) =
      kaplanYorkeDimension 5 (radialPairSpectrum r s).rates := by
  exact local_dimension_eq_of_constant_rates system _ _
    (fun t ht => equilibrium_finiteTimeLE_all r s ht ha hb)

lemma exists_radialType (z : ℂ) (hz : ‖z‖ ^ 2 = 0 ∨ ‖z‖ ^ 2 = 1 ∨ ‖z‖ ^ 2 = 2) :
    ∃ r : RadialType, ∃ a : ℂ, ‖a‖ = 1 ∧ z = r.point a ∧ (z = 0 ↔ r = .zero) := by
  rcases hz with hz | hz | hz
  · have hz₀ : z = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg z])
    exact ⟨.zero, 1, by simp, hz₀, by simp [hz₀]⟩
  · have hn : ‖z‖ = 1 := by nlinarith [norm_nonneg z]
    have hz₀ : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
    exact ⟨.one, z, hn, rfl, by simp [hz₀]⟩
  · have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hn : ‖z‖ = Real.sqrt 2 := by
      apply (sq_eq_sq₀ (norm_nonneg z) hs.le).mp
      rw [hz, Real.sq_sqrt (by norm_num)]
    have hz₀ : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hs.ne')
    refine ⟨.two, (Real.sqrt 2)⁻¹ • z, ?_, ?_, by simp [hz₀]⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), hn, inv_mul_cancel₀ hs.ne']
    · simp [RadialType.point, smul_smul, hs.ne']

lemma recurrent_local_dimension_le_three {x : X}
    (hx : StationarySolution flow x ∨ PeriodicSolution flow x) :
    localLyapunovDimension system x ≤ 3 := by
  have hclass : (q₁ x = 0 ∨ q₁ x = 1 ∨ q₁ x = 2) ∧
      (q₂ x = 0 ∨ q₂ x = 1 ∨ q₂ x = 2) ∧ (fstC x = 0 ∨ sndC x = 0) ∧ x 4 = 0 := by
    rcases hx with hx | hx
    · have hz := (stationary_iff_zero x).mp hx
      subst x
      simp [q₁, q₂, fstC, sndC]
    · exact periodic_candidate_classification hx
  obtain ⟨r, a, ha, hxa, hra⟩ := exists_radialType (fstC x) (by rw [norm_fstC_sq]; exact hclass.1)
  obtain ⟨s, b, hb, hxb, hsb⟩ := exists_radialType (sndC x) (by rw [norm_sndC_sq]; exact hclass.2.1)
  have hrs : r = .zero ∨ s = .zero := hclass.2.2.1.imp hra.mp hsb.mp
  have heq : x = pack (r.point a) (s.point b) 0 := by
    rw [← hxa, ← hxb, ← hclass.2.2.2]
    exact (pack_coordinates x).symm
  rw [heq, equilibrium_local_dimension r s ha hb]
  rcases hrs with rfl | rfl
  · cases s <;> simp only [radialPairSpectrum, SpectrumType.rates,
      spectrum_AA_dimension, spectrum_AB_dimension, spectrum_AC_dimension] <;> norm_num
  · cases r <;> simp only [radialPairSpectrum, SpectrumType.rates,
      spectrum_AA_dimension, spectrum_AB_dimension, spectrum_AC_dimension] <;> norm_num

lemma finiteTime_set_dimension_lower : (9 : ℝ) / 2 ≤ lyapunovDimension system K := by
  have hK : K.Nonempty := nonempty_T.mono T_subset_K
  have hb : IsBoundedUnder (· ≤ ·) atTop
      (fun t : ℝ => finiteTimeLyapunovDimension system t K) :=
    isBoundedUnder_of ⟨5, fun t => finiteTimeLyapunovDimension_le system K hK t⟩
  apply le_liminf_of_le hb.isCobounded_ge
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  obtain ⟨x, hx⟩ := nonempty_T
  have hbounded : BddAbove (finiteTimeLocalLyapunovDimension system t '' K) := by
    refine ⟨5, ?_⟩
    rintro d ⟨y, _, rfl⟩
    exact kaplanYorkeDimension_le 5 _
  have hle := le_csSup hbounded
    (Set.mem_image_of_mem (finiteTimeLocalLyapunovDimension system t) (T_subset_K hx))
  simpa only [finiteTimeLyapunovDimension, finiteTimeLocalLyapunovDimension, torus_finiteTimeLE_all ht hx,
    spectrum_BB_dimension] using hle

theorem modern_no_attainment :
    ¬ ∃ x ∈ K, (StationarySolution system.φ x ∨ system.UnstablePeriodicOrbit x) ∧
      Orbit system.φ x ⊆ K ∧ localLyapunovDimension system x = lyapunovDimension system K := by
  apply no_modern_attainment_of_gap system K 3
  · linarith [finiteTime_set_dimension_lower]
  · intro x _ hx
    exact recurrent_local_dimension_le_three hx

theorem modern_refutation :
    ¬ (∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
      ∀ A : Set (PhaseSpace n), D.GlobalAttractor A →
        ∃ x ∈ A, (StationarySolution D.φ x ∨ D.UnstablePeriodicOrbit x) ∧ Orbit D.φ x ⊆ A ∧
          localLyapunovDimension D x = lyapunovDimension D A) := by
  intro h
  exact modern_no_attainment (h 5 (by norm_num) system K system_globalAttractor)

end PolynomialCounterexample
end Eden
