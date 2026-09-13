import EdensConjecture.EStatementDefinitions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate

namespace Eden
namespace PolynomialCounterexample

abbrev X := PhaseSpace 5

def q₁ (x : X) : ℝ := x 0 ^ 2 + x 1 ^ 2
def q₂ (x : X) : ℝ := x 2 ^ 2 + x 3 ^ 2
def g (q : ℝ) : ℝ := (q - 1) * (2 - q)
def h (r : ℝ) : ℝ := r * g (r ^ 2)

/-- Centering the squared radius at one reduces the radial equation to
the explicitly solvable equation u' = 2u(1-u²). -/
def radialDenominator (t a : ℝ) : ℝ :=
  a ^ 2 + (1 - a ^ 2) * Real.exp (-4 * t)

def shiftedRadius (t a : ℝ) : ℝ := a / Real.sqrt (radialDenominator t a)

def squaredRadius (t q : ℝ) : ℝ := 1 + shiftedRadius t (q - 1)

lemma centered_radial_equation (q : ℝ) :
    2 * q * g q = 2 * (q - 1) * (1 - (q - 1) ^ 2) := by
  unfold g
  ring

lemma radialDenominator_pos {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    0 < radialDenominator t a := by
  have he : Real.exp (-4 * t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp := Real.exp_pos (-4 * t)
  have hm := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr he)
  unfold radialDenominator
  nlinarith

@[simp] lemma shiftedRadius_zero (a : ℝ) : shiftedRadius 0 a = a := by
  simp [shiftedRadius, radialDenominator]

@[simp] lemma squaredRadius_zero (q : ℝ) : squaredRadius 0 q = q := by
  simp [squaredRadius]

@[simp] lemma squaredRadius_at_zero (t : ℝ) : squaredRadius t 0 = 0 := by
  norm_num [squaredRadius, shiftedRadius, radialDenominator]

@[simp] lemma squaredRadius_at_one (t : ℝ) : squaredRadius t 1 = 1 := by
  norm_num [squaredRadius, shiftedRadius]

@[simp] lemma squaredRadius_at_two (t : ℝ) : squaredRadius t 2 = 2 := by
  norm_num [squaredRadius, shiftedRadius, radialDenominator]

lemma radialDenominator_sub_sq (t a : ℝ) :
    radialDenominator t a - a ^ 2 = (1 - a ^ 2) * Real.exp (-4 * t) := by
  simp [radialDenominator]

lemma shiftedRadius_sign {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    (0 < shiftedRadius t a ↔ 0 < a) ∧
    (shiftedRadius t a = 0 ↔ a = 0) := by
  have hs := Real.sqrt_pos.mpr (radialDenominator_pos ht a)
  constructor
  · exact div_pos_iff_of_pos_right hs
  · simp [shiftedRadius, hs.ne']

lemma squaredRadius_pos {t q : ℝ} (ht : 0 ≤ t) (hq : 0 < q) :
    0 < squaredRadius t q := by
  have hd := radialDenominator_pos ht (q - 1)
  have hs := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt hd.le
  unfold squaredRadius shiftedRadius
  by_cases hq₁ : 1 ≤ q
  · have : 0 ≤ (q - 1) / Real.sqrt (radialDenominator t (q - 1)) :=
      div_nonneg (sub_nonneg.mpr hq₁) hs.le
    linarith

  · have hq₁' : q < 1 := lt_of_not_ge hq₁
    have hc : 0 < 1 - (q - 1) ^ 2 := by nlinarith
    have hdiff := radialDenominator_sub_sq t (q - 1)
    have hp := mul_pos hc (Real.exp_pos (-4 * t))
    have habs : 1 - q < Real.sqrt (radialDenominator t (q - 1)) := by
      nlinarith
    have hdiv : -1 < (q - 1) / Real.sqrt (radialDenominator t (q - 1)) := by
      apply (lt_div_iff₀ hs).mpr
      linarith
    linarith

lemma hasDerivAt_radialDenominator (t a : ℝ) :
    HasDerivAt (fun s : ℝ => radialDenominator s a)
      ((1 - a ^ 2) * (Real.exp (-4 * t) * (-4))) t := by
  have he := (Real.hasDerivAt_exp (-4 * t)).comp t
    ((hasDerivAt_id t).const_mul (-4))
  convert (he.const_mul (1 - a ^ 2)).const_add (a ^ 2) using 1 <;> first | rfl | ring

lemma hasDerivAt_shiftedRadius {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    HasDerivAt (fun s : ℝ => shiftedRadius s a)
      (2 * shiftedRadius t a * (1 - shiftedRadius t a ^ 2)) t := by
  have hd := radialDenominator_pos ht a
  have hs : Real.sqrt (radialDenominator t a) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hd)
  have hsq := Real.sq_sqrt hd.le
  have hroot := (hasDerivAt_radialDenominator t a).sqrt hd.ne'
  have hquot := (hasDerivAt_const t a).div hroot hs
  convert hquot using 1 <;> first | rfl | skip
  unfold shiftedRadius
  field_simp [hs]
  unfold radialDenominator at hsq ⊢
  simp only [neg_mul] at hsq ⊢
  linear_combination 4 * a * hsq

lemma hasDerivAt_squaredRadius {t : ℝ} (ht : 0 ≤ t) (q : ℝ) :
    HasDerivAt (fun s : ℝ => squaredRadius s q)
      (2 * squaredRadius t q * g (squaredRadius t q)) t := by
  have hh := (hasDerivAt_shiftedRadius ht (q - 1)).const_add 1
  convert hh using 1 <;> first | rfl | skip
  rw [centered_radial_equation]
  simp [squaredRadius]

lemma tendsto_radialDenominator (a : ℝ) :
    Tendsto (fun t : ℝ => radialDenominator t a) atTop (𝓝 (a ^ 2)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-4 * t)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact (tendsto_const_mul_atBot_of_neg (by norm_num : (-4 : ℝ) < 0)).mpr tendsto_id
  simpa [radialDenominator] using
    (tendsto_const_nhds.add (tendsto_const_nhds.mul he) :
      Tendsto (fun t : ℝ => a ^ 2 + (1 - a ^ 2) * Real.exp (-4 * t))
        atTop (𝓝 (a ^ 2 + (1 - a ^ 2) * 0)))

lemma tendsto_shiftedRadius {a : ℝ} (ha : a ≠ 0) :
    Tendsto (fun t : ℝ => shiftedRadius t a) atTop (𝓝 (a / |a|)) := by
  have hs := (Real.continuous_sqrt.tendsto (a ^ 2)).comp (tendsto_radialDenominator a)
  rw [Real.sqrt_sq_eq_abs] at hs
  exact tendsto_const_nhds.div hs (abs_ne_zero.mpr ha)

lemma tendsto_squaredRadius_below_one {q : ℝ} (hq : q < 1) :
    Tendsto (fun t : ℝ => squaredRadius t q) atTop (𝓝 0) := by
  have hn : q - 1 < 0 := by linarith
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_shiftedRadius hn.ne)
  have heq : (1 : ℝ) + (q - 1) / |q - 1| = 0 := by
    rw [abs_of_neg hn, div_neg, div_self hn.ne]
    norm_num
  rw [heq] at hh
  exact hh

lemma tendsto_squaredRadius_above_one {q : ℝ} (hq : 1 < q) :
    Tendsto (fun t : ℝ => squaredRadius t q) atTop (𝓝 2) := by
  have hp : 0 < q - 1 := by linarith
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_shiftedRadius hp.ne')
  have heq : (1 : ℝ) + (q - 1) / |q - 1| = 2 := by
    rw [abs_of_pos hp, div_self hp.ne']
    norm_num
  rw [heq] at hh
  exact hh

lemma radialDenominator_comp {s : ℝ} (hs : 0 ≤ s) (t a : ℝ) :
    radialDenominator t (shiftedRadius s a) * radialDenominator s a =
      radialDenominator (t + s) a := by
  have hd := radialDenominator_pos hs a
  have hsq := Real.sq_sqrt hd.le
  change ((a / Real.sqrt (radialDenominator s a)) ^ 2 +
    (1 - (a / Real.sqrt (radialDenominator s a)) ^ 2) * Real.exp (-4 * t)) *
      radialDenominator s a = radialDenominator (t + s) a
  rw [div_pow, hsq]
  field_simp [hd.ne']
  unfold radialDenominator
  rw [show -4 * (t + s) = -4 * t + -4 * s by ring, Real.exp_add]
  ring

lemma shiftedRadius_comp {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (a : ℝ) :
    shiftedRadius t (shiftedRadius s a) = shiftedRadius (t + s) a := by
  have hd := radialDenominator_pos ht (shiftedRadius s a)
  have hroot : Real.sqrt (radialDenominator (t + s) a) =
      Real.sqrt (radialDenominator t (shiftedRadius s a)) *
        Real.sqrt (radialDenominator s a) := by
    rw [← radialDenominator_comp hs t a, Real.sqrt_mul hd.le]
  conv_rhs => unfold shiftedRadius
  rw [hroot]
  conv_lhs => unfold shiftedRadius
  rw [shiftedRadius, div_div, mul_comm]

lemma squaredRadius_comp {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (q : ℝ) :
    squaredRadius t (squaredRadius s q) = squaredRadius (t + s) q := by
  simp only [squaredRadius, add_sub_cancel_left]
  rw [shiftedRadius_comp ht hs]

lemma squaredRadius_nonneg {t q : ℝ} (ht : 0 ≤ t) (hq : 0 ≤ q) :
    0 ≤ squaredRadius t q := by
  rcases hq.eq_or_lt with rfl | hq'
  · simp
  · exact (squaredRadius_pos ht hq').le

lemma squaredRadius_le_two {t q : ℝ} (ht : 0 ≤ t) (hq : q ≤ 2) :
    squaredRadius t q ≤ 2 := by
  have hd := radialDenominator_pos ht (q - 1)
  have hs := Real.sqrt_pos.mpr hd
  unfold squaredRadius shiftedRadius
  by_cases hq₁ : q ≤ 1
  · have hdiv : (q - 1) / Real.sqrt (radialDenominator t (q - 1)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
    linarith
  · have hq₁' : 1 < q := lt_of_not_ge hq₁
    have hc : 0 ≤ 1 - (q - 1) ^ 2 := by nlinarith
    have hp := mul_nonneg hc (Real.exp_pos (-4 * t)).le
    have hdiff := radialDenominator_sub_sq t (q - 1)
    have hsq := Real.sq_sqrt hd.le
    have hle : q - 1 ≤ Real.sqrt (radialDenominator t (q - 1)) := by
      nlinarith
    have hdiv : (q - 1) / Real.sqrt (radialDenominator t (q - 1)) ≤ 1 :=
      (div_le_one hs).mpr hle
    linarith

lemma squaredRadius_mapsTo_interval {t : ℝ} (ht : 0 ≤ t) :
    MapsTo (squaredRadius t) (Icc 0 2) (Icc 0 2) := by
  intro q hq
  exact ⟨squaredRadius_nonneg ht hq.1, squaredRadius_le_two ht hq.2⟩

/-- The real polynomial field corresponding to the two complex equations. -/
def vectorField (x : X) : X := WithLp.toLp 2
  ![g (q₁ x) * x 0 - x 1, g (q₁ x) * x 1 + x 0,
    g (q₂ x) * x 2 - Real.sqrt 2 * x 3,
    g (q₂ x) * x 3 + Real.sqrt 2 * x 2, -8 * x 4]

def K : Set X := {x | q₁ x ≤ 2 ∧ q₂ x ≤ 2 ∧ x 4 = 0}
def T : Set X := {x | q₁ x = 1 ∧ q₂ x = 1 ∧ x 4 = 0}

lemma q₁_nonneg (x : X) : 0 ≤ q₁ x := add_nonneg (sq_nonneg _) (sq_nonneg _)
lemma q₂_nonneg (x : X) : 0 ≤ q₂ x := add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma T_subset_K : T ⊆ K := by
  rintro x ⟨h₁, h₂, h₃⟩
  exact ⟨by linarith, by linarith, h₃⟩

lemma norm_sq (x : X) : ‖x‖ ^ 2 = q₁ x + q₂ x + x 4 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [q₁, q₂, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  ring

lemma isClosed_K : IsClosed K := by
  have hc₁ : Continuous q₁ := by unfold q₁; fun_prop
  have hc₂ : Continuous q₂ := by unfold q₂; fun_prop
  exact (isClosed_le hc₁ continuous_const).inter
    ((isClosed_le hc₂ continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const))

lemma isCompact_K : IsCompact K := by
  apply (Metric.isCompact_iff_isClosed_bounded).mpr
  refine ⟨isClosed_K, isBounded_iff_forall_norm_le.mpr ⟨2, ?_⟩⟩
  rintro x ⟨hx₁, hx₂, hx₄⟩
  have hn := norm_sq x
  rw [hx₄] at hn
  nlinarith [norm_nonneg x]

lemma nonempty_K : K.Nonempty := by
  exact ⟨0, by norm_num [K, q₁, q₂]⟩

lemma angular_identity₁ (x : X) :
    x 0 * vectorField x 1 - x 1 * vectorField x 0 = q₁ x := by
  simp [vectorField, q₁]
  ring

lemma angular_identity₂ (x : X) :
    x 2 * vectorField x 3 - x 3 * vectorField x 2 = Real.sqrt 2 * q₂ x := by
  simp [vectorField, q₂]
  ring

lemma vectorField_eq_zero_iff (x : X) : vectorField x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h₁ := angular_identity₁ x
    have h₂ := angular_identity₂ x
    rw [hx] at h₁ h₂
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hq₁ : q₁ x = 0 := by simpa using h₁.symm
    have hq₂ : q₂ x = 0 := by
      have hz : Real.sqrt 2 * q₂ x = 0 := by simpa using h₂.symm
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hs)
    have h₄ : -8 * x 4 = 0 := by
      simpa [vectorField] using congrArg (fun y : X => y 4) hx
    unfold q₁ at hq₁
    unfold q₂ at hq₂
    have hz₀ : x 0 = 0 := by nlinarith [sq_nonneg (x 1)]
    have hz₁ : x 1 = 0 := by nlinarith [sq_nonneg (x 0)]
    have hz₂ : x 2 = 0 := by nlinarith [sq_nonneg (x 3)]
    have hz₃ : x 3 = 0 := by nlinarith [sq_nonneg (x 2)]
    have hz₄ : x 4 = 0 := by linarith
    ext i
    fin_cases i <;> simpa using (by assumption : x _ = 0)
  · rintro rfl
    ext i
    fin_cases i <;> norm_num [vectorField, q₁, q₂, g]

lemma contDiff_vectorField : ContDiff ℝ ⊤ vectorField := by
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i <;> simp [vectorField, q₁, q₂, g] <;> fun_prop

lemma radial_derivative (r : ℝ) :
    HasDerivAt h (-5 * (r ^ 2) ^ 2 + 9 * r ^ 2 - 2) r := by
  convert ((hasDerivAt_id r).mul
    ((((hasDerivAt_id r).pow 2).sub_const 1).mul
      ((hasDerivAt_const r (2 : ℝ)).sub ((hasDerivAt_id r).pow 2)))) using 1 <;>
    first | rfl | (dsimp [h, g]; ring)

lemma radial_rate_lower_bound {q : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q ≤ 2) :
    -4 ≤ -5 * q ^ 2 + 9 * q - 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq₂) (show 0 ≤ 5 * q + 1 by linarith)]

lemma tangential_rate_lower_bound {q : ℝ} (hq₀ : 0 ≤ q) (hq₂ : q ≤ 2) :
    -2 ≤ g q := by
  unfold g
  nlinarith [mul_nonneg hq₀ (show 0 ≤ 3 - q by linarith)]

lemma block_trace_identity (q : ℝ) :
    (-5 * q ^ 2 + 9 * q - 2) + g q = 2 - 6 * (q - 1) ^ 2 := by
  unfold g
  ring

lemma total_trace_identity (a b : ℝ) :
    ((-5 * a ^ 2 + 9 * a - 2) + g a) +
      ((-5 * b ^ 2 + 9 * b - 2) + g b) - 8 =
        -4 - 6 * ((a - 1) ^ 2 + (b - 1) ^ 2) := by
  rw [block_trace_identity, block_trace_identity]
  ring

lemma total_trace_le (a b : ℝ) :
    -4 - 6 * ((a - 1) ^ 2 + (b - 1) ^ 2) ≤ -4 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]

lemma total_trace_eq_iff (a b : ℝ) :
    -4 - 6 * ((a - 1) ^ 2 + (b - 1) ^ 2) = -4 ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro heq
    constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1)]
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- The exponent lists in the source note, indexed from zero. -/
def spectrum (a b c d e : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then a else if i = 1 then b else if i = 2 then c
  else if i = 3 then d else if i = 4 then e else 0

/-- A finite check of the defining supremum, with no assumed sorting lemma. -/
lemma kaplanYorkeIndex_eq_of_sums (n j : ℕ) (rates : ℕ → ℝ)
    (hj : j ≤ n) (hpos : 0 ≤ exponentSum rates j)
    (hneg : ∀ k, j < k → k ≤ n → exponentSum rates k < 0) :
    kaplanYorkeIndex n rates = j := by
  unfold kaplanYorkeIndex
  apply le_antisymm
  · apply csSup_le
    · exact ⟨j, hj, hpos⟩
    · intro k hk
      by_contra hkj
      exact (not_lt_of_ge hk.2) (hneg k (lt_of_not_ge hkj) hk.1)
  · apply le_csSup
    · exact ⟨n, fun k hk => hk.1⟩
    · exact ⟨hj, hpos⟩

lemma spectrum_AA_dimension :
    kaplanYorkeDimension 5 (spectrum (-2) (-2) (-2) (-2) (-8)) = 0 := by
  have hi : kaplanYorkeIndex 5 (spectrum (-2) (-2) (-2) (-2) (-8)) = 0 := by
    apply kaplanYorkeIndex_eq_of_sums <;> norm_num [exponentSum]
    intro k hk hk'
    interval_cases k <;> norm_num [exponentSum, spectrum, Finset.sum_range_succ]
  norm_num [kaplanYorkeDimension, hi, exponentSum]

lemma spectrum_AB_dimension :
    kaplanYorkeDimension 5 (spectrum 2 0 (-2) (-2) (-8)) = 3 := by
  have hi : kaplanYorkeIndex 5 (spectrum 2 0 (-2) (-2) (-8)) = 3 := by
    apply kaplanYorkeIndex_eq_of_sums <;>
      norm_num [exponentSum, spectrum, Finset.sum_range_succ]
    intro k hk hk'
    interval_cases k <;> norm_num [exponentSum, spectrum, Finset.sum_range_succ]
  norm_num [kaplanYorkeDimension, hi, exponentSum, spectrum, Finset.sum_range_succ]

lemma spectrum_AC_dimension :
    kaplanYorkeDimension 5 (spectrum 0 (-2) (-2) (-4) (-8)) = 1 := by
  have hi : kaplanYorkeIndex 5 (spectrum 0 (-2) (-2) (-4) (-8)) = 1 := by
    apply kaplanYorkeIndex_eq_of_sums <;>
      norm_num [exponentSum, spectrum, Finset.sum_range_succ]
    intro k hk hk'
    interval_cases k <;> norm_num [exponentSum, spectrum, Finset.sum_range_succ]
  norm_num [kaplanYorkeDimension, hi, exponentSum, spectrum, Finset.sum_range_succ]

lemma spectrum_BB_dimension :
    kaplanYorkeDimension 5 (spectrum 2 2 0 0 (-8)) = 9 / 2 := by
  have hi : kaplanYorkeIndex 5 (spectrum 2 2 0 0 (-8)) = 4 := by
    apply kaplanYorkeIndex_eq_of_sums <;>
      norm_num [exponentSum, spectrum, Finset.sum_range_succ]
    intro k hk hk'
    interval_cases k <;> norm_num [exponentSum, spectrum, Finset.sum_range_succ]
  norm_num [kaplanYorkeDimension, hi, exponentSum, spectrum, Finset.sum_range_succ]

lemma spectrum_BC_dimension :
    kaplanYorkeDimension 5 (spectrum 2 0 0 (-4) (-8)) = 7 / 2 := by
  have hi : kaplanYorkeIndex 5 (spectrum 2 0 0 (-4) (-8)) = 3 := by
    apply kaplanYorkeIndex_eq_of_sums <;>
      norm_num [exponentSum, spectrum, Finset.sum_range_succ]
    intro k hk hk'
    interval_cases k <;> norm_num [exponentSum, spectrum, Finset.sum_range_succ]
  norm_num [kaplanYorkeDimension, hi, exponentSum, spectrum, Finset.sum_range_succ]

lemma spectrum_CC_dimension :
    kaplanYorkeDimension 5 (spectrum 0 0 (-4) (-4) (-8)) = 2 := by
  have hi : kaplanYorkeIndex 5 (spectrum 0 0 (-4) (-4) (-8)) = 2 := by
    apply kaplanYorkeIndex_eq_of_sums <;>
      norm_num [exponentSum, spectrum, Finset.sum_range_succ]
    intro k hk hk'
    interval_cases k <;> norm_num [exponentSum, spectrum, Finset.sum_range_succ]
  norm_num [kaplanYorkeDimension, hi, exponentSum, spectrum, Finset.sum_range_succ]

/-- The thesis uses N = 4 even where the pointwise KY index is smaller.
In particular the periodic AB spectrum gives 15/4, not 3. -/
lemma thesis_AB_ratio :
    (4 : ℝ) + exponentSum (spectrum 2 0 (-2) (-2) (-8)) 4 / |(-8 : ℝ)| = 15 / 4 := by
  norm_num [exponentSum, spectrum, Finset.sum_range_succ]

lemma thesis_AA_AC_CC_ratio :
    (4 : ℝ) + (-8) / |(-8 : ℝ)| = 3 := by norm_num

lemma thesis_BB_ratio :
    (4 : ℝ) + exponentSum (spectrum 2 2 0 0 (-8)) 4 / |(-8 : ℝ)| = 9 / 2 := by
  norm_num [exponentSum, spectrum, Finset.sum_range_succ]

/-- The six possible unordered pairs of radial asymptotic types. -/
inductive SpectrumType where
  | AA | AB | AC | BB | BC | CC
  deriving DecidableEq

def SpectrumType.rates : SpectrumType → ℕ → ℝ
  | .AA => spectrum (-2) (-2) (-2) (-2) (-8)
  | .AB => spectrum 2 0 (-2) (-2) (-8)
  | .AC => spectrum 0 (-2) (-2) (-4) (-8)
  | .BB => spectrum 2 2 0 0 (-8)
  | .BC => spectrum 2 0 0 (-4) (-8)
  | .CC => spectrum 0 0 (-4) (-4) (-8)

lemma SpectrumType.fifth_rate (s : SpectrumType) : s.rates 4 = -8 := by
  cases s <;> norm_num [SpectrumType.rates, spectrum]

lemma SpectrumType.sum_five_neg (s : SpectrumType) : exponentSum s.rates 5 < 0 := by
  cases s <;> norm_num [SpectrumType.rates, exponentSum, spectrum, Finset.sum_range_succ]

lemma SpectrumType.sum_four_le (s : SpectrumType) : exponentSum s.rates 4 ≤ 4 := by
  cases s <;> norm_num [SpectrumType.rates, exponentSum, spectrum, Finset.sum_range_succ]

lemma SpectrumType.thesis_ratio_le (s : SpectrumType) :
    (4 : ℝ) + exponentSum s.rates 4 / |s.rates 4| ≤ 9 / 2 := by
  rw [s.fifth_rate]
  have := s.sum_four_le
  norm_num
  linarith

lemma SpectrumType.thesis_ratio_eq_iff (s : SpectrumType) :
    (4 : ℝ) + exponentSum s.rates 4 / |s.rates 4| = 9 / 2 ↔ s = .BB := by
  cases s <;> norm_num [SpectrumType.rates, exponentSum, spectrum, Finset.sum_range_succ] <;> decide

lemma SpectrumType.modern_dimension_le (s : SpectrumType) :
    kaplanYorkeDimension 5 s.rates ≤ 9 / 2 := by
  cases s <;> simp only [SpectrumType.rates, spectrum_AA_dimension,
    spectrum_AB_dimension, spectrum_AC_dimension, spectrum_BB_dimension,
    spectrum_BC_dimension, spectrum_CC_dimension] <;> norm_num

lemma SpectrumType.modern_dimension_eq_iff (s : SpectrumType) :
    kaplanYorkeDimension 5 s.rates = 9 / 2 ↔ s = .BB := by
  cases s <;> simp only [SpectrumType.rates, spectrum_AA_dimension,
    spectrum_AB_dimension, spectrum_AC_dimension, spectrum_BB_dimension,
    spectrum_BC_dimension, spectrum_CC_dimension] <;> norm_num <;> decide

/-- This is the scalar expression to be identified with the actual
singular-value function, for 4 ≤ d ≤ 5, via the variational equation. -/
def volumeTail (d t integral : ℝ) : ℝ :=
  Real.exp ((36 - 8 * d) * t - 6 * integral)

lemma volumeTail_at_dimension (t integral : ℝ) :
    volumeTail (9 / 2) t integral = Real.exp (-6 * integral) := by
  unfold volumeTail
  congr 1
  ring

lemma volumeTail_le_one (t : ℝ) {integral : ℝ} (hi : 0 ≤ integral) :
    volumeTail (9 / 2) t integral ≤ 1 := by
  rw [volumeTail_at_dimension, Real.exp_le_one_iff]
  linarith

lemma volumeTail_eq_one_iff (t integral : ℝ) :
    volumeTail (9 / 2) t integral = 1 ↔ integral = 0 := by
  rw [volumeTail_at_dimension, Real.exp_eq_one_iff]
  constructor <;> intro hi <;> linarith

lemma volumeTail_lt_one_above {d t integral : ℝ}
    (hd : 9 / 2 < d) (ht : 0 < t) (hi : 0 ≤ integral) :
    volumeTail d t integral < 1 := by
  rw [volumeTail, Real.exp_lt_one_iff]
  have hm : (36 - 8 * d) * t < 0 :=
    mul_neg_of_neg_of_pos (by linarith) ht
  linarith

/-- Algebraic threshold on the torus, where the integral vanishes. -/
lemma volumeTail_torus_eq (d t : ℝ) :
    volumeTail d t 0 = Real.exp ((36 - 8 * d) * t) := by
  simp [volumeTail]

/-- The final modern contradiction only needs a strict gap at recurrent
candidates and one point above that gap, together with boundedness. -/
lemma no_modern_attainment_of_gap {n : ℕ} (D : C1DynamicalSystem n)
    (A : Set (PhaseSpace n)) (c : ℝ)
    (hbounded : BddAbove (localLyapunovDimension D '' A))
    (hlarge : ∃ p ∈ A, c < localLyapunovDimension D p)
    (hsmall : ∀ p ∈ A, StationarySolution D.φ p ∨ PeriodicSolution D.φ p →
      localLyapunovDimension D p ≤ c) :
    ¬ ∃ p ∈ A,
      (StationarySolution D.φ p ∨ D.UnstablePeriodicOrbit p) ∧
      Orbit D.φ p ⊆ A ∧
      localLyapunovDimension D p = sSup (localLyapunovDimension D '' A) := by
  rintro ⟨p, hp, hrec, _, heq⟩
  have hpdim : localLyapunovDimension D p ≤ c :=
    hsmall p hp (hrec.elim Or.inl (fun h => Or.inr h.1))
  rcases hlarge with ⟨q, hq, hqdim⟩
  have hle := le_csSup hbounded (Set.mem_image_of_mem (localLyapunovDimension D) hq)
  rw [← heq] at hle
  exact (not_lt_of_ge (hle.trans hpdim)) hqdim

/-- The thesis contradiction uses its own local dimension and extended-real
supremum; no identification with pointwise Kaplan--Yorke is assumed. -/
lemma no_thesis_attainment_of_gap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (D : ThesisSetting H)
    (N : ℕ) (μ : ℕ → H → ℝ) (c : ℝ)
    (hlarge : ∃ p ∈ D.X, c < D.localLyapunovDimension N μ p)
    (hsmall : ∀ p ∈ D.X, StationarySolution D.S p ∨ PeriodicSolution D.S p →
      D.localLyapunovDimension N μ p ≤ c) :
    ¬ D.StationaryOrPeriodicSupremumAttainment N μ := by
  rintro ⟨p, hp, hrec, heq⟩
  rcases hlarge with ⟨q, hq, hqdim⟩
  have hle : (D.localLyapunovDimension N μ q : EReal) ≤
      D.supremumLocalLyapunovDimension N μ :=
    le_sSup (Set.mem_image_of_mem _ hq)
  rw [← heq] at hle
  have hreal : D.localLyapunovDimension N μ q ≤ D.localLyapunovDimension N μ p :=
    EReal.coe_le_coe_iff.mp hle
  exact (not_lt_of_ge (hreal.trans (hsmall p hp hrec))) hqdim

lemma no_thesis_recurrent_critical_path_of_gap {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (D : ThesisSetting H)
    (N : ℕ) (μ : ℕ → H → ℝ) (c : ℝ)
    (hbound : (c : EReal) < D.douadyOesterleDimension N)
    (hsmall : ∀ p ∈ D.X, StationarySolution D.S p ∨ PeriodicSolution D.S p →
      D.localLyapunovDimension N μ p ≤ c) :
    ¬ ∃ p, D.CriticalPath N μ p ∧
      (StationarySolution D.S p ∨ PeriodicSolution D.S p) := by
  rintro ⟨p, ⟨hp, hcrit⟩, hrec⟩
  have hle : (D.localLyapunovDimension N μ p : EReal) ≤ (c : EReal) :=
    EReal.coe_le_coe_iff.mpr (hsmall p hp hrec)
  exact (not_lt_of_ge (hcrit.trans hle)) hbound

/-! ## The full solution operator -/

def radius (t r : ℝ) : ℝ := Real.sqrt (squaredRadius t (r ^ 2))

lemma radius_nonneg (t r : ℝ) : 0 ≤ radius t r := Real.sqrt_nonneg _

lemma radius_pos {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) : 0 < radius t r :=
  Real.sqrt_pos.mpr (squaredRadius_pos ht (sq_pos_of_pos hr))

@[simp] lemma radius_at_zero (t : ℝ) : radius t 0 = 0 := by simp [radius]

lemma radius_zero {r : ℝ} (hr : 0 ≤ r) : radius 0 r = r := by
  simp [radius, Real.sqrt_sq hr]

lemma radius_sq {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    radius t r ^ 2 = squaredRadius t (r ^ 2) :=
  Real.sq_sqrt (squaredRadius_nonneg ht (sq_nonneg r))

lemma radius_comp {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (r : ℝ) :
    radius t (radius s r) = radius (t + s) r := by
  unfold radius
  rw [Real.sq_sqrt (squaredRadius_nonneg hs (sq_nonneg r)), squaredRadius_comp ht hs]

lemma hasDerivAt_radius {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => radius s r)
      (radius t r * g (radius t r ^ 2)) t := by
  have hq := squaredRadius_pos ht (sq_pos_of_pos hr)
  have hh := (hasDerivAt_squaredRadius ht (r ^ 2)).sqrt hq.ne'
  convert hh using 1 <;> first | rfl | skip
  rw [← radius_sq ht]
  rw [Real.sqrt_sq (radius_nonneg t r)]
  change radius t r * g (radius t r ^ 2) =
    (2 * radius t r ^ 2 * g (radius t r ^ 2)) / (2 * radius t r)
  field_simp [ne_of_gt (radius_pos ht hr)]

def phase (omega t : ℝ) : ℂ := Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I)

lemma norm_phase (omega t : ℝ) : ‖phase omega t‖ = 1 := by
  simp [phase, Complex.norm_exp]

@[simp] lemma phase_zero (omega : ℝ) : phase omega 0 = 1 := by simp [phase]

lemma phase_add (omega t s : ℝ) : phase omega (t + s) = phase omega t * phase omega s := by
  simp [phase, mul_add, Complex.exp_add, add_mul]

def blockFlow (omega t : ℝ) (z : ℂ) : ℂ :=
  ((radius t ‖z‖ / ‖z‖ : ℝ) : ℂ) * phase omega t * z

def blockField (omega : ℝ) (z : ℂ) : ℂ :=
  ((g (‖z‖ ^ 2) : ℂ) + (omega : ℂ) * Complex.I) * z

@[simp] lemma blockFlow_at_zero (omega t : ℝ) : blockFlow omega t 0 = 0 := by
  simp [blockFlow]

@[simp] lemma blockField_at_zero (omega : ℝ) : blockField omega 0 = 0 := by
  simp [blockField]

@[simp] lemma blockFlow_zero (omega : ℝ) (z : ℂ) : blockFlow omega 0 z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [blockFlow, radius_zero (norm_nonneg z), div_self (norm_ne_zero_iff.mpr hz)]
    simp

lemma norm_blockFlow (omega t : ℝ) (z : ℂ) : ‖blockFlow omega t z‖ = radius t ‖z‖ := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [blockFlow, norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg (radius_nonneg t ‖z‖) hn.le),
      div_mul_cancel₀ _ hn.ne']

lemma blockFlow_comp (omega : ℝ) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (z : ℂ) :
    blockFlow omega t (blockFlow omega s z) = blockFlow omega (t + s) z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn := norm_pos_iff.mpr hz
    have hr := radius_pos hs hn
    change ((radius t ‖blockFlow omega s z‖ / ‖blockFlow omega s z‖ : ℝ) : ℂ) *
      phase omega t * blockFlow omega s z = blockFlow omega (t + s) z
    rw [norm_blockFlow, radius_comp ht hs]
    simp only [blockFlow, phase_add]
    push_cast
    field_simp [ne_of_gt hn, ne_of_gt hr]

lemma hasDerivAt_phase (omega t : ℝ) :
    HasDerivAt (fun s : ℝ => phase omega s)
      (phase omega t * ((omega : ℂ) * Complex.I)) t := by
  have hlin : HasDerivAt (fun s : ℝ => ((omega * s : ℝ) : ℂ)) (omega : ℂ) t := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul omega).ofReal_comp
  exact (hlin.mul_const Complex.I).cexp

lemma hasDerivAt_blockFlow (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    HasDerivAt (fun s : ℝ => blockFlow omega s z)
      (blockField omega (blockFlow omega t z)) t := by
  by_cases hz : z = 0
  · subst z
    simpa using hasDerivAt_const t (0 : ℂ)
  · have hn := norm_pos_iff.mpr hz
    have hr := (hasDerivAt_radius ht hn).ofReal_comp
    have hscale : HasDerivAt (fun s : ℝ => ((radius s ‖z‖ / ‖z‖ : ℝ) : ℂ))
        (((radius t ‖z‖ * g (radius t ‖z‖ ^ 2)) / ‖z‖ : ℝ) : ℂ) t := by
      convert hr.div_const (‖z‖ : ℂ) using 1 <;> first | rfl | (push_cast; rfl)
    have hh := (hscale.mul (hasDerivAt_phase omega t)).mul_const z
    convert hh using 1 <;> first | rfl | skip
    rw [blockField, norm_blockFlow]
    unfold blockFlow
    push_cast
    ring

def fstC (x : X) : ℂ := (x 0 : ℂ) + (x 1 : ℂ) * Complex.I
def sndC (x : X) : ℂ := (x 2 : ℂ) + (x 3 : ℂ) * Complex.I
def pack (z w : ℂ) (v : ℝ) : X := WithLp.toLp 2 ![z.re, z.im, w.re, w.im, v]

@[simp] lemma fstC_pack (z w : ℂ) (v : ℝ) : fstC (pack z w v) = z := by
  apply Complex.ext <;> simp [fstC, pack]

@[simp] lemma sndC_pack (z w : ℂ) (v : ℝ) : sndC (pack z w v) = w := by
  apply Complex.ext <;> simp [sndC, pack]

@[simp] lemma fifth_pack (z w : ℂ) (v : ℝ) : pack z w v 4 = v := rfl

@[simp] lemma pack_coordinates (x : X) : pack (fstC x) (sndC x) (x 4) = x := by
  ext i
  fin_cases i <;> simp [pack, fstC, sndC]

lemma norm_fstC_sq (x : X) : ‖fstC x‖ ^ 2 = q₁ x := by
  rw [Complex.sq_norm]
  simp [fstC, q₁, Complex.normSq_apply, pow_two]

lemma norm_sndC_sq (x : X) : ‖sndC x‖ ^ 2 = q₂ x := by
  rw [Complex.sq_norm]
  simp [sndC, q₂, Complex.normSq_apply, pow_two]

def flow (t : ℝ) (x : X) : X :=
  pack (blockFlow 1 t (fstC x)) (blockFlow (Real.sqrt 2) t (sndC x))
    (Real.exp (-8 * t) * x 4)

@[simp] lemma flow_zero (x : X) : flow 0 x = x := by simp [flow]

lemma flow_comp {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (x : X) :
    flow t (flow s x) = flow (t + s) x := by
  simp only [flow, fstC_pack, sndC_pack, fifth_pack, blockFlow_comp _ ht hs]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

lemma vectorField_pack (z w : ℂ) (v : ℝ) :
    vectorField (pack z w v) = pack (blockField 1 z) (blockField (Real.sqrt 2) w) (-8 * v) := by
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  have hw : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  simp only [blockField, hz, hw]
  ext i
  fin_cases i <;>
    simp [vectorField, pack, q₁, q₂] <;> ring

lemma q₁_flow {t : ℝ} (ht : 0 ≤ t) (x : X) :
    q₁ (flow t x) = squaredRadius t (q₁ x) := by
  rw [← norm_fstC_sq, flow, fstC_pack, norm_blockFlow, radius_sq ht, norm_fstC_sq]

lemma q₂_flow {t : ℝ} (ht : 0 ≤ t) (x : X) :
    q₂ (flow t x) = squaredRadius t (q₂ x) := by
  rw [← norm_sndC_sq, flow, sndC_pack, norm_blockFlow, radius_sq ht, norm_sndC_sq]

lemma flow_mapsTo_K {t : ℝ} (ht : 0 ≤ t) : MapsTo (flow t) K K := by
  rintro x ⟨hx₁, hx₂, hx₄⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [q₁_flow ht]
    exact squaredRadius_le_two ht hx₁
  · rw [q₂_flow ht]
    exact squaredRadius_le_two ht hx₂
  · simp [flow, hx₄]

lemma flow_mapsTo_T {t : ℝ} (ht : 0 ≤ t) : MapsTo (flow t) T T := by
  rintro x ⟨hx₁, hx₂, hx₄⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [q₁_flow ht, hx₁, squaredRadius_at_one]
  · rw [q₂_flow ht, hx₂, squaredRadius_at_one]
  · simp [flow, hx₄]

lemma hasDerivAt_pack {z w : ℝ → ℂ} {v : ℝ → ℝ} {z' w' : ℂ} {v' t : ℝ}
    (hz : HasDerivAt z z' t) (hw : HasDerivAt w w' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => pack (z s) (w s) (v s)) (pack z' w' v') t := by
  have hh : HasDerivAt (fun s => ![(z s).re, (z s).im, (w s).re, (w s).im, v s])
      ![z'.re, z'.im, w'.re, w'.im, v'] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
    · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
    · exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hw
    · exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hw
    · exact hv
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 5 => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hh

lemma flow_solves_ODE {t : ℝ} (ht : 0 ≤ t) (x : X) :
    HasDerivAt (fun s : ℝ => flow s x) (vectorField (flow t x)) t := by
  have hv : HasDerivAt (fun s : ℝ => Real.exp (-8 * s) * x 4)
      (-8 * (Real.exp (-8 * t) * x 4)) t := by
    have hh := ((Real.hasDerivAt_exp (-8 * t)).comp t
      ((hasDerivAt_id t).const_mul (-8))).mul_const (x 4)
    convert hh using 1 <;> first | rfl | ring
  have hh := hasDerivAt_pack (hasDerivAt_blockFlow 1 ht (fstC x))
    (hasDerivAt_blockFlow (Real.sqrt 2) ht (sndC x)) hv
  convert hh using 1 <;> first | rfl | skip
  exact vectorField_pack _ _ _

lemma squaredRadius_eq_self_iff {t : ℝ} (ht : 0 < t) (q : ℝ) :
    squaredRadius t q = q ↔ q = 0 ∨ q = 1 ∨ q = 2 := by
  constructor
  · intro hret
    by_cases ha : q - 1 = 0
    · exact Or.inr (Or.inl (by linarith))
    · have hd := radialDenominator_pos ht.le (q - 1)
      have hs := Real.sqrt_pos.mpr hd
      have hsq := Real.sq_sqrt hd.le
      have hdiv : (q - 1) / Real.sqrt (radialDenominator t (q - 1)) = q - 1 := by
        unfold squaredRadius shiftedRadius at hret
        linarith
      have hmul := (div_eq_iff hs.ne').mp hdiv
      have hs₁ : Real.sqrt (radialDenominator t (q - 1)) = 1 := by
        have hh : (q - 1) * (Real.sqrt (radialDenominator t (q - 1)) - 1) = 0 := by
          nlinarith
        have := (mul_eq_zero.mp hh).resolve_left ha
        linarith
      rw [hs₁] at hsq
      have he : Real.exp (-4 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hf : ((q - 1) ^ 2 - 1) * (1 - Real.exp (-4 * t)) = 0 := by
        unfold radialDenominator at hsq
        nlinarith
      have hh := (mul_eq_zero.mp hf).resolve_right (by linarith)
      have hh' : (q - 1) ^ 2 = 1 := by linarith
      rcases sq_eq_one_iff.mp hh' with hpos | hneg
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl (by linarith)
  · rintro (rfl | rfl | rfl) <;> simp

lemma phase_eq_one_of_return (omega : ℝ) {t : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hret : blockFlow omega t z = z) : phase omega t = 1 := by
  have hr : radius t ‖z‖ = ‖z‖ := by
    simpa only [norm_blockFlow] using congrArg norm hret
  rw [blockFlow, hr, div_self (norm_ne_zero_iff.mpr hz)] at hret
  simp only [Complex.ofReal_one, one_mul] at hret
  exact mul_right_cancel₀ hz (by simpa using hret)

lemma no_return_of_both_nonzero {x : X} (hx₁ : fstC x ≠ 0) (hx₂ : sndC x ≠ 0)
    {t : ℝ} (ht : 0 < t) : flow t x ≠ x := by
  intro hret
  have hr₁ : blockFlow 1 t (fstC x) = fstC x := by
    simpa only [flow, fstC_pack] using congrArg fstC hret
  have hr₂ : blockFlow (Real.sqrt 2) t (sndC x) = sndC x := by
    simpa only [flow, sndC_pack] using congrArg sndC hret
  have hc₁ : Real.cos t = 1 := by
    have hh := congrArg Complex.re (phase_eq_one_of_return 1 hx₁ hr₁)
    simpa [phase, Complex.exp_re] using hh
  have hc₂ : Real.cos (Real.sqrt 2 * t) = 1 := by
    have hh := congrArg Complex.re (phase_eq_one_of_return (Real.sqrt 2) hx₂ hr₂)
    simpa [phase, Complex.exp_re] using hh
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff t).mp hc₁
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (Real.sqrt 2 * t)).mp hc₂
  have hm₀ : (m : ℝ) ≠ 0 := by
    intro hh
    rw [hh, zero_mul] at hm
    linarith
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hrel : (n : ℝ) = Real.sqrt 2 * (m : ℝ) := by
    apply mul_right_cancel₀ hpi
    calc
      (n : ℝ) * (2 * Real.pi) = Real.sqrt 2 * t := hn
      _ = Real.sqrt 2 * ((m : ℝ) * (2 * Real.pi)) := by rw [hm]
      _ = (Real.sqrt 2 * (m : ℝ)) * (2 * Real.pi) := by ring
  have hrat : Real.sqrt 2 = (n : ℝ) / (m : ℝ) := by
    rw [eq_div_iff hm₀]
    exact hrel.symm
  exact irrational_sqrt_two.ne_rational n m hrat

lemma no_positive_return_on_T {x : X} (hx : x ∈ T) {t : ℝ} (ht : 0 < t) :
    flow t x ≠ x := by
  have hn₁ := norm_fstC_sq x
  have hn₂ := norm_sndC_sq x
  rw [hx.1] at hn₁
  rw [hx.2.1] at hn₂
  apply no_return_of_both_nonzero _ _ ht
  · intro hh
    simp [hh] at hn₁
  · intro hh
    simp [hh] at hn₂

lemma no_stationary_on_T {x : X} (hx : x ∈ T) : ¬ StationarySolution flow x := by
  intro hh
  exact no_positive_return_on_T hx one_pos (hh 1 zero_le_one)

lemma no_periodic_on_T {x : X} (hx : x ∈ T) : ¬ PeriodicSolution flow x := by
  rintro ⟨_, t, ht, hperiod⟩
  exact no_positive_return_on_T hx ht (by simpa using hperiod 0 le_rfl)

lemma positive_return_classification {x : X} {t : ℝ} (ht : 0 < t)
    (hret : flow t x = x) :
    (q₁ x = 0 ∨ q₁ x = 1 ∨ q₁ x = 2) ∧
    (q₂ x = 0 ∨ q₂ x = 1 ∨ q₂ x = 2) ∧
    (fstC x = 0 ∨ sndC x = 0) ∧ x 4 = 0 := by
  have hr₁ : squaredRadius t (q₁ x) = q₁ x := by
    simpa only [q₁_flow ht.le] using congrArg q₁ hret
  have hr₂ : squaredRadius t (q₂ x) = q₂ x := by
    simpa only [q₂_flow ht.le] using congrArg q₂ hret
  refine ⟨(squaredRadius_eq_self_iff ht _).mp hr₁,
    (squaredRadius_eq_self_iff ht _).mp hr₂, ?_, ?_⟩
  · by_contra hh
    push_neg at hh
    exact no_return_of_both_nonzero hh.1 hh.2 ht hret
  · have hv : Real.exp (-8 * t) * x 4 = x 4 := by
      simpa [flow] using congrArg (fun y : X => y 4) hret
    have he : Real.exp (-8 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hh : (Real.exp (-8 * t) - 1) * x 4 = 0 := by nlinarith
    exact (mul_eq_zero.mp hh).resolve_left (by linarith)

/-! The division by ‖z‖ in `blockFlow` is removable at zero. This rationalized
formula makes that fact explicit, so smoothness at zero is proved rather
than inferred from smoothness away from the origin. -/

def regularScaleSq (t q : ℝ) : ℝ :=
  (2 - q) * Real.exp (-4 * t) /
    (Real.sqrt (radialDenominator t (q - 1)) *
      (Real.sqrt (radialDenominator t (q - 1)) - (q - 1)))

lemma regularScaleSq_pos {t q : ℝ} (ht : 0 ≤ t) (hq : q < 1) :
    0 < regularScaleSq t q := by
  have hs := Real.sqrt_pos.mpr (radialDenominator_pos ht (q - 1))
  exact div_pos (mul_pos (by linarith) (Real.exp_pos _))
    (mul_pos hs (by linarith))

lemma regularScaleSq_mul {t q : ℝ} (ht : 0 ≤ t) (hq : q < 1) :
    regularScaleSq t q * q = squaredRadius t q := by
  have hd := radialDenominator_pos ht (q - 1)
  have hs := Real.sqrt_pos.mpr hd
  have hs' : Real.sqrt (radialDenominator t (q - 1)) - (q - 1) ≠ 0 := by
    linarith
  have hsq := Real.sq_sqrt hd.le
  unfold regularScaleSq squaredRadius shiftedRadius
  field_simp [hs.ne', hs']
  unfold radialDenominator at hsq ⊢
  simp only [neg_mul] at hsq ⊢
  linear_combination -hsq

lemma blockFlow_eq_regular {t : ℝ} (ht : 0 ≤ t) (omega : ℝ) {z : ℂ}
    (hz : ‖z‖ ^ 2 < 1) :
    blockFlow omega t z = (Real.sqrt (regularScaleSq t (‖z‖ ^ 2)) : ℂ) * phase omega t * z := by
  by_cases hz₀ : z = 0
  · simp [hz₀]
  · have hn := norm_pos_iff.mpr hz₀
    have hq := sq_pos_of_pos hn
    have hreg := regularScaleSq_pos ht hz
    have hh := regularScaleSq_mul ht hz
    have hscale : radius t ‖z‖ / ‖z‖ = Real.sqrt (regularScaleSq t (‖z‖ ^ 2)) := by
      apply (sq_eq_sq₀ (div_nonneg (radius_nonneg _ _) hn.le) (Real.sqrt_nonneg _)).mp
      rw [div_pow, radius_sq ht, Real.sq_sqrt hreg.le]
      exact (div_eq_iff hq.ne').mpr hh.symm
    rw [blockFlow, hscale]

lemma contDiff_squaredRadius {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ⊤ (squaredRadius t) := by
  have hd : ContDiff ℝ ⊤ (fun q : ℝ => radialDenominator t (q - 1)) := by
    unfold radialDenominator
    fun_prop
  have hs := hd.sqrt (fun q => (radialDenominator_pos ht (q - 1)).ne')
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).div hs
    (fun q => (Real.sqrt_pos.mpr (radialDenominator_pos ht (q - 1))).ne'))

lemma contDiffAt_regularScaleSq {t q : ℝ} (ht : 0 ≤ t) (hq : q < 1) :
    ContDiffAt ℝ ⊤ (regularScaleSq t) q := by
  have hd : ContDiff ℝ ⊤ (fun q : ℝ => radialDenominator t (q - 1)) := by
    unfold radialDenominator
    fun_prop
  have hs := hd.sqrt (fun q => (radialDenominator_pos ht (q - 1)).ne')
  have hp := Real.sqrt_pos.mpr (radialDenominator_pos ht (q - 1))
  have hden : Real.sqrt (radialDenominator t (q - 1)) *
      (Real.sqrt (radialDenominator t (q - 1)) - (q - 1)) ≠ 0 :=
    mul_ne_zero hp.ne' (by linarith)
  exact ((contDiffAt_const.sub contDiffAt_id).mul contDiffAt_const).div
    (hs.contDiffAt.mul (hs.contDiffAt.sub (contDiffAt_id.sub contDiffAt_const))) hden

lemma contDiff_blockFlow (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ⊤ (blockFlow omega t) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have hreg := (contDiffAt_regularScaleSq ht (by norm_num : (0 : ℝ) < 1)).sqrt
      (regularScaleSq_pos ht (by norm_num : (0 : ℝ) < 1)).ne'
    have hq : ContDiffAt ℝ ⊤ (fun z : ℂ => ‖z‖ ^ 2) 0 := (contDiff_norm_sq ℂ).contDiffAt
    have hscale : ContDiffAt ℝ ⊤ (fun z : ℂ => Real.sqrt (regularScaleSq t (‖z‖ ^ 2))) 0 := by
      have hg : ContDiffAt ℝ ⊤ (fun q => Real.sqrt (regularScaleSq t q)) (‖(0 : ℂ)‖ ^ 2) := by
        simpa using hreg
      have hh := hg.comp (0 : ℂ) hq
      convert hh using 1 <;> rfl
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ) hscale
    have hh := (hc.mul (contDiffAt_const (c := phase omega t))).mul contDiffAt_id
    apply hh.congr_of_eventuallyEq
    have he : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ ^ 2 < 1 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by norm_num)
    filter_upwards [he] with z hz
    exact blockFlow_eq_regular ht omega hz
  · have hn := norm_pos_iff.mpr hz
    have hnorm : ContDiffAt ℝ ⊤ (fun z : ℂ => ‖z‖) z := contDiffAt_norm ℝ hz
    have hq := (contDiff_squaredRadius ht).contDiffAt.comp z (contDiff_norm_sq ℂ).contDiffAt
    have hr := hq.sqrt (squaredRadius_pos ht (sq_pos_of_pos hn)).ne'
    have hscale := hr.div hnorm hn.ne'
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hscale
    have hh := (hc.mul (contDiffAt_const (c := phase omega t))).mul contDiffAt_id
    convert hh using 1 <;> rfl

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

lemma contDiff_pack : ContDiff ℝ ⊤ (fun p : ℂ × ℂ × ℝ => pack p.1 p.2.1 p.2.2) := by
  apply PiLp.contDiff_toLp.comp
  rw [contDiff_pi]
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ × ℝ => Complex.reCLM p.1)
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ × ℝ => Complex.imCLM p.1)
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ × ℝ => Complex.reCLM p.2.1)
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ × ℝ => Complex.imCLM p.2.1)
    fun_prop
  · change ContDiff ℝ ⊤ (fun p : ℂ × ℂ × ℝ => p.2.2)
    fun_prop

lemma contDiff_flow {t : ℝ} (ht : 0 ≤ t) : ContDiff ℝ ⊤ (flow t) := by
  have hp : ContDiff ℝ ⊤ (fun x : X =>
      (blockFlow 1 t (fstC x), blockFlow (Real.sqrt 2) t (sndC x), Real.exp (-8 * t) * x 4)) := by
    apply ContDiff.prodMk
    · exact (contDiff_blockFlow 1 ht).comp contDiff_fstC
    · apply ContDiff.prodMk
      · exact (contDiff_blockFlow (Real.sqrt 2) ht).comp contDiff_sndC
      · fun_prop
  convert contDiff_pack.comp hp using 1 <;> rfl

lemma continuousAt_jointSquaredRadius {p : ℝ × ℝ} (ht : 0 ≤ p.1) :
    ContinuousAt (fun q : ℝ × ℝ => squaredRadius q.1 q.2) p := by
  have hd : Continuous (fun q : ℝ × ℝ => Real.sqrt (radialDenominator q.1 (q.2 - 1))) := by
    unfold radialDenominator
    fun_prop
  have hh := (continuousAt_const (y := (1 : ℝ))).add
    ((continuous_snd.sub (continuous_const (y := (1 : ℝ)))).continuousAt.div hd.continuousAt
      (Real.sqrt_pos.mpr (radialDenominator_pos ht (p.2 - 1))).ne')
  convert hh using 1 <;> rfl

lemma continuousAt_jointRegularScaleSq {p : ℝ × ℝ} (ht : 0 ≤ p.1) (hq : p.2 < 1) :
    ContinuousAt (fun q : ℝ × ℝ => regularScaleSq q.1 q.2) p := by
  have hd : Continuous (fun q : ℝ × ℝ => Real.sqrt (radialDenominator q.1 (q.2 - 1))) := by
    unfold radialDenominator
    fun_prop
  have hp := Real.sqrt_pos.mpr (radialDenominator_pos ht (p.2 - 1))
  have hden : Real.sqrt (radialDenominator p.1 (p.2 - 1)) *
      (Real.sqrt (radialDenominator p.1 (p.2 - 1)) - (p.2 - 1)) ≠ 0 :=
    mul_ne_zero hp.ne' (by linarith)
  have hn : Continuous (fun q : ℝ × ℝ => (2 - q.2) * Real.exp (-4 * q.1)) := by fun_prop
  have hh := hn.continuousAt.div
    (hd.mul (hd.sub (continuous_snd.sub continuous_const))).continuousAt hden
  convert hh using 1 <;> rfl

lemma continuousOn_jointBlockFlow (omega : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ => blockFlow omega p.1 p.2) ((Ici 0) ×ˢ univ) := by
  intro p hp
  have hcoord : Continuous (fun r : ℝ × ℂ => (r.1, ‖r.2‖ ^ 2)) := by fun_prop
  have hphase : Continuous (fun r : ℝ × ℂ => phase omega r.1) := by
    unfold phase
    fun_prop
  by_cases hz : p.2 = 0
  · have hq : ‖p.2‖ ^ 2 < 1 := by simp [hz]
    have hreg := (continuousAt_jointRegularScaleSq (p := (p.1, ‖p.2‖ ^ 2)) hp.1 hq).comp
      (f := fun r : ℝ × ℂ => (r.1, ‖r.2‖ ^ 2)) hcoord.continuousAt
    have hs := Real.continuous_sqrt.continuousAt.comp hreg
    have hc := Complex.continuous_ofReal.continuousAt.comp hs
    have hh := (hc.mul hphase.continuousAt).mul continuous_snd.continuousAt
    apply hh.continuousWithinAt.congr_of_eventuallyEq_of_mem _ hp
    have he : ∀ᶠ r : ℝ × ℂ in 𝓝 p, ‖r.2‖ ^ 2 < 1 :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds hq
    filter_upwards [self_mem_nhdsWithin, he.filter_mono nhdsWithin_le_nhds] with r hr hrq
    exact blockFlow_eq_regular hr.1 omega hrq
  · have hrad := (continuousAt_jointSquaredRadius (p := (p.1, ‖p.2‖ ^ 2)) hp.1).comp
      (f := fun r : ℝ × ℂ => (r.1, ‖r.2‖ ^ 2)) hcoord.continuousAt
    have hs := (Real.continuous_sqrt.continuousAt.comp hrad).div
      continuous_snd.norm.continuousAt (norm_ne_zero_iff.mpr hz)
    have hc := Complex.continuous_ofReal.continuousAt.comp hs
    have hh := (hc.mul hphase.continuousAt).mul continuous_snd.continuousAt
    convert hh.continuousWithinAt using 1 <;> rfl

lemma continuousOn_jointFlow :
    ContinuousOn (fun p : ℝ × X => flow p.1 p.2) ((Ici 0) ×ˢ univ) := by
  have hf : Continuous (fun p : ℝ × X => (p.1, fstC p.2)) :=
    continuous_fst.prodMk (contDiff_fstC.continuous.comp continuous_snd)
  have hg : Continuous (fun p : ℝ × X => (p.1, sndC p.2)) :=
    continuous_fst.prodMk (contDiff_sndC.continuous.comp continuous_snd)
  have h₁ := (continuousOn_jointBlockFlow 1).comp hf.continuousOn
    (show MapsTo (fun p : ℝ × X => (p.1, fstC p.2)) ((Ici 0) ×ˢ univ) ((Ici 0) ×ˢ univ) from
      fun p hp => ⟨hp.1, mem_univ _⟩)
  have h₂ := (continuousOn_jointBlockFlow (Real.sqrt 2)).comp hg.continuousOn
    (show MapsTo (fun p : ℝ × X => (p.1, sndC p.2)) ((Ici 0) ×ˢ univ) ((Ici 0) ×ˢ univ) from
      fun p hp => ⟨hp.1, mem_univ _⟩)
  have hv : Continuous (fun p : ℝ × X => Real.exp (-8 * p.1) * p.2 4) := by fun_prop
  have hh := contDiff_pack.continuous.comp_continuousOn (h₁.prodMk (h₂.prodMk hv.continuousOn))
  convert hh using 1 <;> rfl

lemma squaredRadius_surjOn_interval {t : ℝ} (ht : 0 ≤ t) :
    SurjOn (squaredRadius t) (Icc 0 2) (Icc 0 2) := by
  have hh := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2)
    (contDiff_squaredRadius ht).continuous.continuousOn
  intro q hq
  exact hh (by simpa using hq)

lemma radius_surjOn_interval {t : ℝ} (ht : 0 ≤ t) {r : ℝ}
    (hr : 0 ≤ r) (hr₂ : r ^ 2 ≤ 2) :
    ∃ a : ℝ, 0 ≤ a ∧ a ^ 2 ≤ 2 ∧ radius t a = r := by
  obtain ⟨q, hq, hqr⟩ := squaredRadius_surjOn_interval ht ⟨sq_nonneg r, hr₂⟩
  refine ⟨Real.sqrt q, Real.sqrt_nonneg q, ?_, ?_⟩
  · rw [Real.sq_sqrt hq.1]
    exact hq.2
  · unfold radius
    rw [Real.sq_sqrt hq.1, hqr, Real.sqrt_sq hr]

lemma blockFlow_surjOn_disk (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : ‖z‖ ^ 2 ≤ 2) :
    ∃ w : ℂ, ‖w‖ ^ 2 ≤ 2 ∧ blockFlow omega t w = z := by
  by_cases hz₀ : z = 0
  · exact ⟨0, by simp, by simp [hz₀]⟩
  · have hn := norm_pos_iff.mpr hz₀
    obtain ⟨a, ha, ha₂, har⟩ := radius_surjOn_interval ht hn.le hz
    have ha₀ : 0 < a := by
      by_contra hh
      have : a = 0 := by linarith
      simp [this] at har
      linarith
    let w : ℂ := ((a / ‖z‖ : ℝ) : ℂ) * phase omega (-t) * z
    have hnorm : ‖w‖ = a := by
      dsimp [w]
      rw [norm_mul, norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg ha hn.le), div_mul_cancel₀ _ hn.ne']
    refine ⟨w, by rw [hnorm]; exact ha₂, ?_⟩
    have hphase : phase omega t * phase omega (-t) = 1 := by
      rw [← phase_add]
      simp
    rw [blockFlow, hnorm, har]
    dsimp [w]
    push_cast
    calc
      _ = (phase omega t * phase omega (-t)) * z := by
        field_simp [hn.ne', ha₀.ne']
      _ = z := by rw [hphase, one_mul]

lemma flow_image_K {t : ℝ} (ht : 0 ≤ t) : flow t '' K = K := by
  apply Set.Subset.antisymm (flow_mapsTo_K ht).image_subset
  intro x hx
  have hz : ‖fstC x‖ ^ 2 ≤ 2 := by rw [norm_fstC_sq]; exact hx.1
  have hw : ‖sndC x‖ ^ 2 ≤ 2 := by rw [norm_sndC_sq]; exact hx.2.1
  obtain ⟨z, hz₂, hzf⟩ := blockFlow_surjOn_disk 1 ht hz
  obtain ⟨w, hw₂, hwf⟩ := blockFlow_surjOn_disk (Real.sqrt 2) ht hw
  refine ⟨pack z w 0, ?_, ?_⟩
  · refine ⟨?_, ?_, rfl⟩
    · rw [← norm_fstC_sq, fstC_pack]
      exact hz₂
    · rw [← norm_sndC_sq, sndC_pack]
      exact hw₂
  · simp only [flow, fstC_pack, sndC_pack, fifth_pack, mul_zero, hzf, hwf]
    rw [← hx.2.2]
    exact pack_coordinates x

lemma stationary_iff_zero (x : X) : StationarySolution flow x ↔ x = 0 := by
  constructor
  · intro hx
    have he : (fun s : ℝ => flow s x) =ᶠ[𝓝 (1 : ℝ)] (fun _ => x) := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with s hs
      exact hx s hs.le
    have hd := (flow_solves_ODE (t := 1) zero_le_one x).congr_of_eventuallyEq he.symm
    have hz : vectorField (flow 1 x) = 0 := hd.unique (hasDerivAt_const 1 x)
    rw [hx 1 zero_le_one] at hz
    exact (vectorField_eq_zero_iff x).mp hz
  · rintro rfl t ht
    simp [flow, fstC, sndC, pack]

lemma periodic_candidate_classification {x : X} (hx : PeriodicSolution flow x) :
    (q₁ x = 0 ∨ q₁ x = 1 ∨ q₁ x = 2) ∧
    (q₂ x = 0 ∨ q₂ x = 1 ∨ q₂ x = 2) ∧
    (fstC x = 0 ∨ sndC x = 0) ∧ x 4 = 0 := by
  obtain ⟨_, t, ht, hperiod⟩ := hx
  exact positive_return_classification ht (by simpa using hperiod 0 le_rfl)

lemma nonempty_T : T.Nonempty := by
  refine ⟨pack 1 1 0, ?_⟩
  change q₁ (pack 1 1 0) = 1 ∧ q₂ (pack 1 1 0) = 1 ∧ pack 1 1 0 4 = 0
  rw [← norm_fstC_sq, ← norm_sndC_sq, fstC_pack, sndC_pack, fifth_pack]
  norm_num

lemma isClosed_T : IsClosed T := by
  have hc₁ : Continuous q₁ := by unfold q₁; fun_prop
  have hc₂ : Continuous q₂ := by unfold q₂; fun_prop
  exact (isClosed_eq hc₁ continuous_const).inter
    ((isClosed_eq hc₂ continuous_const).inter
      (isClosed_eq (by fun_prop) continuous_const))

lemma isCompact_T : IsCompact T := isCompact_K.of_isClosed_subset isClosed_T T_subset_K

def radialExcessBound (t : ℝ) : ℝ :=
  Real.sqrt (1 + (Real.sqrt (1 - Real.exp (-4 * t)))⁻¹) - Real.sqrt 2

lemma squaredRadius_uniform_bound {t : ℝ} (ht : 0 < t) (q : ℝ) :
    squaredRadius t q ≤ 1 + (Real.sqrt (1 - Real.exp (-4 * t)))⁻¹ := by
  have he : Real.exp (-4 * t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hc : 0 < 1 - Real.exp (-4 * t) := by linarith
  have hs := Real.sqrt_pos.mpr hc
  have hd := radialDenominator_pos ht.le (q - 1)
  have hd' := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt hd.le
  have hsq' := Real.sq_sqrt hc.le
  unfold squaredRadius shiftedRadius
  by_cases hq : q ≤ 1
  · have hh := div_nonpos_of_nonpos_of_nonneg (show q - 1 ≤ 0 by linarith) hd'.le
    have hi := inv_pos.mpr hs
    linarith
  · have hq' : 0 ≤ q - 1 := by linarith
    have hprod : (q - 1) * Real.sqrt (1 - Real.exp (-4 * t)) ≤
        Real.sqrt (radialDenominator t (q - 1)) := by
      apply (sq_le_sq₀ (mul_nonneg hq' hs.le) hd'.le).mp
      rw [mul_pow, hsq, hsq']
      unfold radialDenominator
      nlinarith [Real.exp_pos (-4 * t)]
    have hquot : (q - 1) / Real.sqrt (radialDenominator t (q - 1)) ≤
        (Real.sqrt (1 - Real.exp (-4 * t)))⁻¹ := by
      rw [inv_eq_one_div, div_le_div_iff₀ hd' hs]
      simpa using hprod
    linarith

lemma radius_uniform_bound {t : ℝ} (ht : 0 < t) (r : ℝ) :
    radius t r ≤ Real.sqrt 2 + radialExcessBound t := by
  have hh := Real.sqrt_le_sqrt (squaredRadius_uniform_bound ht (r ^ 2))
  simpa [radius, radialExcessBound] using hh

lemma radialExcessBound_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ radialExcessBound t := by
  have hh := radius_uniform_bound ht (Real.sqrt 2)
  have heq : radius t (Real.sqrt 2) = Real.sqrt 2 := by
    simp [radius, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq] at hh
  linarith

lemma tendsto_radialExcessBound : Tendsto radialExcessBound atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-4 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (by norm_num : (-4 : ℝ) < 0)).mpr tendsto_id)
  have hc := (tendsto_const_nhds (x := (1 : ℝ))).sub he
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hc
  have hi := hs.inv₀ (by norm_num : Real.sqrt ((1 : ℝ) - 0) ≠ 0)
  have ha := (tendsto_const_nhds (x := (1 : ℝ))).add hi
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ha
  have hh := hr.sub (tendsto_const_nhds (x := Real.sqrt 2))
  norm_num at hh
  convert hh using 1
  funext t
  simp [radialExcessBound, neg_mul]

def diskProjection (z : ℂ) : ℂ :=
  if ‖z‖ ≤ Real.sqrt 2 then z else ((Real.sqrt 2 / ‖z‖ : ℝ) : ℂ) * z

lemma norm_diskProjection_le (z : ℂ) : ‖diskProjection z‖ ≤ Real.sqrt 2 := by
  unfold diskProjection
  split_ifs with hz
  · exact hz
  · have hn : 0 < ‖z‖ := lt_trans (Real.sqrt_pos.mpr (by norm_num)) (lt_of_not_ge hz)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hn.le), div_mul_cancel₀ _ hn.ne']

lemma dist_diskProjection_le {z : ℂ} {e : ℝ} (he : 0 ≤ e)
    (hz : ‖z‖ ≤ Real.sqrt 2 + e) : dist z (diskProjection z) ≤ e := by
  unfold diskProjection
  split_ifs with hzn
  · simpa using he
  · have hn : 0 < ‖z‖ := lt_trans (Real.sqrt_pos.mpr (by norm_num)) (lt_of_not_ge hzn)
    have hquot : Real.sqrt 2 / ‖z‖ ≤ 1 := (div_le_one hn).mpr (le_of_not_ge hzn)
    rw [dist_eq_norm, show z - ((Real.sqrt 2 / ‖z‖ : ℝ) : ℂ) * z =
      ((1 - Real.sqrt 2 / ‖z‖ : ℝ) : ℂ) * z by push_cast; ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have heq : (1 - Real.sqrt 2 / ‖z‖) * ‖z‖ = ‖z‖ - Real.sqrt 2 := by
      field_simp
    rw [heq]
    linarith

lemma norm_pack_sq (z w : ℂ) (v : ℝ) :
    ‖pack z w v‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + v ^ 2 := by
  rw [norm_sq, ← norm_fstC_sq, ← norm_sndC_sq, fstC_pack, sndC_pack, fifth_pack]

lemma norm_pack_le (z w : ℂ) (v : ℝ) : ‖pack z w v‖ ≤ ‖z‖ + ‖w‖ + |v| := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_pack_sq]
  nlinarith [sq_abs v, mul_nonneg (norm_nonneg z) (norm_nonneg w),
    mul_nonneg (norm_nonneg z) (abs_nonneg v), mul_nonneg (norm_nonneg w) (abs_nonneg v)]

lemma pack_sub (z w z' w' : ℂ) (v v' : ℝ) :
    pack z w v - pack z' w' v' = pack (z - z') (w - w') (v - v') := by
  ext i
  fin_cases i <;> simp [pack]

def comparisonPoint (t : ℝ) (x : X) : X :=
  pack (diskProjection (blockFlow 1 t (fstC x)))
    (diskProjection (blockFlow (Real.sqrt 2) t (sndC x))) 0

lemma comparisonPoint_mem_K (t : ℝ) (x : X) : comparisonPoint t x ∈ K := by
  refine ⟨?_, ?_, rfl⟩
  · rw [← norm_fstC_sq, comparisonPoint, fstC_pack]
    have hh := sq_le_sq₀ (norm_nonneg (diskProjection (blockFlow 1 t (fstC x))))
      (Real.sqrt_nonneg 2)
    have hs := hh.mpr (norm_diskProjection_le _)
    simpa using hs
  · rw [← norm_sndC_sq, comparisonPoint, sndC_pack]
    have hh := sq_le_sq₀ (norm_nonneg (diskProjection (blockFlow (Real.sqrt 2) t (sndC x))))
      (Real.sqrt_nonneg 2)
    have hs := hh.mpr (norm_diskProjection_le _)
    simpa using hs

lemma dist_flow_comparison_le {t : ℝ} (ht : 0 < t) (x : X) :
    dist (flow t x) (comparisonPoint t x) ≤
      2 * radialExcessBound t + Real.exp (-8 * t) * |x 4| := by
  have hz := dist_diskProjection_le (z := blockFlow 1 t (fstC x)) (radialExcessBound_nonneg ht)
    (by rw [norm_blockFlow]; exact radius_uniform_bound ht ‖fstC x‖)
  have hw := dist_diskProjection_le (z := blockFlow (Real.sqrt 2) t (sndC x)) (radialExcessBound_nonneg ht)
    (by rw [norm_blockFlow]; exact radius_uniform_bound ht ‖sndC x‖)
  rw [dist_eq_norm, flow, comparisonPoint, pack_sub]
  have hh := norm_pack_le
    (blockFlow 1 t (fstC x) - diskProjection (blockFlow 1 t (fstC x)))
    (blockFlow (Real.sqrt 2) t (sndC x) - diskProjection (blockFlow (Real.sqrt 2) t (sndC x)))
    (Real.exp (-8 * t) * x 4 - 0)
  simp only [sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)] at hh ⊢
  rw [dist_eq_norm] at hz hw
  linarith

lemma uniformlyAttracts_K (B : Set X) (hB : Bornology.IsBounded B) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      ∀ t : ℝ, T ≤ t → ∀ x ∈ B, ∃ y ∈ K, dist (flow t x) y < ε := by
  obtain ⟨M, hM⟩ := hB.exists_norm_le
  have he : Tendsto (fun t : ℝ => Real.exp (-8 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (by norm_num : (-8 : ℝ) < 0)).mpr tendsto_id)
  have hlimit : Tendsto (fun t : ℝ => 2 * radialExcessBound t + Real.exp (-8 * t) * M)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_radialExcessBound).add
      (he.mul (tendsto_const_nhds (x := M)))
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlimit.eventually_lt_const hε)
  refine ⟨max 1 T, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro t ht x hx
  have ht₀ : 0 < t := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans ht)
  refine ⟨comparisonPoint t x, comparisonPoint_mem_K t x, ?_⟩
  have hcoord : |x 4| ≤ M := by
    have hh := PiLp.norm_apply_le x (4 : Fin 5)
    have hh' : |x 4| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using hh
    exact hh'.trans (hM x hx)
  have hbound := dist_flow_comparison_le ht₀ x
  have hmul := mul_le_mul_of_nonneg_left hcoord (Real.exp_pos (-8 * t)).le
  have hsmall := hT t ((le_max_right _ _).trans ht)
  linarith

lemma hasDerivAt_squaredRadius_initial {t : ℝ} (ht : 0 ≤ t) (q : ℝ) :
    HasDerivAt (squaredRadius t)
      (Real.exp (-4 * t) / (Real.sqrt (radialDenominator t (q - 1))) ^ 3) q := by
  have hd := radialDenominator_pos ht (q - 1)
  have hs := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt hd.le
  have ha : HasDerivAt (fun q : ℝ => q - 1) 1 q := (hasDerivAt_id q).sub_const 1
  have hden : HasDerivAt (fun q : ℝ => radialDenominator t (q - 1))
      (2 * (q - 1) * (1 - Real.exp (-4 * t))) q := by
    have hh := (ha.pow 2).add
      (((hasDerivAt_const q (1 : ℝ)).sub (ha.pow 2)).mul_const (Real.exp (-4 * t)))
    convert hh using 1 <;> first | rfl | ring
  have hh := (ha.div (hden.sqrt hd.ne') hs.ne').const_add 1
  convert hh using 1 <;> first | rfl | skip
  field_simp [hs.ne']
  unfold radialDenominator at hsq ⊢
  simp only [neg_mul] at hsq ⊢
  nlinarith [hsq]

lemma squaredRadius_initial_derivative_pos {t : ℝ} (ht : 0 ≤ t) (q : ℝ) :
    0 < deriv (squaredRadius t) q := by
  rw [(hasDerivAt_squaredRadius_initial ht q).deriv]
  exact div_pos (Real.exp_pos _) (pow_pos (Real.sqrt_pos.mpr (radialDenominator_pos ht _)) 3)

lemma strictMono_squaredRadius {t : ℝ} (ht : 0 ≤ t) : StrictMono (squaredRadius t) :=
  strictMono_of_deriv_pos (fun q => squaredRadius_initial_derivative_pos ht q)

lemma radialDenominator_reverse {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    radialDenominator (-t) (shiftedRadius t a) = (radialDenominator t a)⁻¹ := by
  have hh := radialDenominator_comp ht (-t) a
  have hd := radialDenominator_pos ht a
  have hzero : radialDenominator 0 a = 1 := by simp [radialDenominator]
  rw [neg_add_cancel, hzero] at hh
  apply (mul_right_cancel₀ hd.ne')
  rw [hh, inv_mul_cancel₀ hd.ne']

lemma shiftedRadius_reverse {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    shiftedRadius (-t) (shiftedRadius t a) = a := by
  have hd := radialDenominator_pos ht a
  have hs := Real.sqrt_pos.mpr hd
  change shiftedRadius t a / Real.sqrt (radialDenominator (-t) (shiftedRadius t a)) = a
  rw [radialDenominator_reverse ht, Real.sqrt_inv, shiftedRadius]
  field_simp [hs.ne']

lemma squaredRadius_reverse {t : ℝ} (ht : 0 ≤ t) (q : ℝ) :
    squaredRadius (-t) (squaredRadius t q) = q := by
  simp only [squaredRadius, add_sub_cancel_left]
  rw [shiftedRadius_reverse ht]
  ring

lemma radius_reverse {t : ℝ} (ht : 0 ≤ t) {r : ℝ} (hr : 0 ≤ r) :
    radius (-t) (radius t r) = r := by
  unfold radius
  rw [Real.sq_sqrt (squaredRadius_nonneg ht (sq_nonneg r)), squaredRadius_reverse ht,
    Real.sqrt_sq hr]

lemma blockFlow_reverse (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    blockFlow omega (-t) (blockFlow omega t z) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · have hn := norm_pos_iff.mpr hz
    have hr := radius_pos ht hn
    change ((radius (-t) ‖blockFlow omega t z‖ / ‖blockFlow omega t z‖ : ℝ) : ℂ) *
      phase omega (-t) * blockFlow omega t z = z
    rw [norm_blockFlow, radius_reverse ht hn.le]
    have hp : phase omega (-t) * phase omega t = 1 := by rw [← phase_add]; simp
    unfold blockFlow
    push_cast
    calc
      _ = (phase omega (-t) * phase omega t) * z := by field_simp [hn.ne', hr.ne']
      _ = z := by rw [hp, one_mul]

lemma flow_reverse {t : ℝ} (ht : 0 ≤ t) (x : X) : flow (-t) (flow t x) = x := by
  simp only [flow, fstC_pack, sndC_pack, fifth_pack, blockFlow_reverse _ ht]
  have he : Real.exp (-8 * -t) * (Real.exp (-8 * t) * x 4) = x 4 := by
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  rw [he, pack_coordinates]

lemma squaredRadius_pos_of_denominator {t q : ℝ}
    (hd : 0 < radialDenominator t (q - 1)) (hq : 0 < q) : 0 < squaredRadius t q := by
  have hs := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt hd.le
  unfold squaredRadius shiftedRadius
  by_cases hq₁ : 1 ≤ q
  · have hh := div_nonneg (show 0 ≤ q - 1 by linarith) hs.le
    linarith
  · have hc : 0 < 1 - (q - 1) ^ 2 := by nlinarith
    have hh := mul_pos hc (Real.exp_pos (-4 * t))
    have hid := radialDenominator_sub_sq t (q - 1)
    have hlt : 1 - q < Real.sqrt (radialDenominator t (q - 1)) := by nlinarith
    have hdiv : -1 < (q - 1) / Real.sqrt (radialDenominator t (q - 1)) := by
      rw [lt_div_iff₀ hs]
      linarith
    linarith

lemma blockFlow_eq_regular_of_denominator {t : ℝ} (omega : ℝ) {z : ℂ}
    (hd : 0 < radialDenominator t (‖z‖ ^ 2 - 1)) (hz : ‖z‖ ^ 2 < 1) :
    blockFlow omega t z = (Real.sqrt (regularScaleSq t (‖z‖ ^ 2)) : ℂ) * phase omega t * z := by
  by_cases hz₀ : z = 0
  · simp [hz₀]
  · have hn := norm_pos_iff.mpr hz₀
    have hq := sq_pos_of_pos hn
    have hs := Real.sqrt_pos.mpr hd
    have hs' : Real.sqrt (radialDenominator t (‖z‖ ^ 2 - 1)) - (‖z‖ ^ 2 - 1) ≠ 0 := by linarith
    have hp : 0 < regularScaleSq t (‖z‖ ^ 2) :=
      div_pos (mul_pos (by linarith) (Real.exp_pos _)) (mul_pos hs (by linarith))
    have hm : regularScaleSq t (‖z‖ ^ 2) * ‖z‖ ^ 2 = squaredRadius t (‖z‖ ^ 2) := by
      have hsq := Real.sq_sqrt hd.le
      unfold regularScaleSq squaredRadius shiftedRadius
      field_simp [hs.ne', hs']
      unfold radialDenominator at hsq ⊢
      simp only [neg_mul] at hsq ⊢
      linear_combination -hsq
    have heq : radius t ‖z‖ / ‖z‖ = Real.sqrt (regularScaleSq t (‖z‖ ^ 2)) := by
      apply (sq_eq_sq₀ (div_nonneg (radius_nonneg _ _) hn.le) (Real.sqrt_nonneg _)).mp
      rw [div_pow, radius, Real.sq_sqrt (squaredRadius_pos_of_denominator hd hq).le,
        Real.sq_sqrt hp.le]
      exact (div_eq_iff hq.ne').mpr hm.symm
    rw [blockFlow, heq]

lemma contDiffAt_blockFlow_of_denominator (omega t : ℝ) (z : ℂ)
    (hd : 0 < radialDenominator t (‖z‖ ^ 2 - 1)) : ContDiffAt ℝ ⊤ (blockFlow omega t) z := by
  have hden : ContDiff ℝ ⊤ (fun z : ℂ => radialDenominator t (‖z‖ ^ 2 - 1)) := by
    have hq : ContDiff ℝ ⊤ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℂ
    unfold radialDenominator
    exact ((hq.sub contDiff_const).pow 2).add
      ((contDiff_const.sub ((hq.sub contDiff_const).pow 2)).mul contDiff_const)
  have hs := hden.contDiffAt.sqrt hd.ne'
  have hspos := Real.sqrt_pos.mpr hd
  have hq : ContDiff ℝ ⊤ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℂ
  by_cases hz : z = 0
  · subst z
    have hreg : ContDiffAt ℝ ⊤ (fun z : ℂ => regularScaleSq t (‖z‖ ^ 2)) 0 := by
      unfold regularScaleSq
      apply ((contDiffAt_const.sub hq.contDiffAt).mul contDiffAt_const).div
        (hs.mul (hs.sub (hq.contDiffAt.sub contDiffAt_const)))
      simp [radialDenominator]
    have hpos : 0 < regularScaleSq t (‖(0 : ℂ)‖ ^ 2) := by
      simp [regularScaleSq, radialDenominator, Real.exp_pos]
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp (0 : ℂ) (hreg.sqrt hpos.ne')
    have hh := (hc.mul (contDiffAt_const (c := phase omega t))).mul contDiffAt_id
    apply hh.congr_of_eventuallyEq
    have he : ∀ᶠ w : ℂ in 𝓝 0, 0 < radialDenominator t (‖w‖ ^ 2 - 1) ∧ ‖w‖ ^ 2 < 1 := by
      have he₁ : ∀ᶠ w : ℂ in 𝓝 0, 0 < radialDenominator t (‖w‖ ^ 2 - 1) :=
        (isOpen_lt continuous_const hden.continuous).mem_nhds hd
      have he₂ : ∀ᶠ w : ℂ in 𝓝 0, ‖w‖ ^ 2 < 1 :=
        (isOpen_lt hq.continuous continuous_const).mem_nhds (by norm_num)
      exact he₁.and he₂
    filter_upwards [he] with w hw
    exact blockFlow_eq_regular_of_denominator omega hw.1 hw.2
  · have hn := norm_pos_iff.mpr hz
    have hrad := (contDiffAt_const.add ((hq.contDiffAt.sub contDiffAt_const).div hs hspos.ne')).sqrt
      (squaredRadius_pos_of_denominator hd (sq_pos_of_pos hn)).ne'
    have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (hrad.div (contDiffAt_norm ℝ hz) hn.ne')
    have hh := (hc.mul (contDiffAt_const (c := phase omega t))).mul contDiffAt_id
    convert hh using 1 <;> rfl

lemma contDiffAt_blockFlow_reverse (omega : ℝ) {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    ContDiffAt ℝ ⊤ (blockFlow omega (-t)) (blockFlow omega t z) := by
  apply contDiffAt_blockFlow_of_denominator
  rw [norm_blockFlow, radius_sq ht]
  simp only [squaredRadius, add_sub_cancel_left]
  rw [radialDenominator_reverse ht]
  exact inv_pos.mpr (radialDenominator_pos ht _)

lemma contDiffAt_flow_reverse {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ContDiffAt ℝ ⊤ (flow (-t)) (flow t x) := by
  have h₁ : ContDiffAt ℝ ⊤ (fun y : X => blockFlow 1 (-t) (fstC y)) (flow t x) := by
    have hh : ContDiffAt ℝ ⊤ (blockFlow 1 (-t)) (fstC (flow t x)) := by
      simpa only [flow, fstC_pack] using contDiffAt_blockFlow_reverse 1 ht (fstC x)
    have hcomp := hh.comp (flow t x) contDiff_fstC.contDiffAt
    convert hcomp using 1 <;> rfl
  have h₂ : ContDiffAt ℝ ⊤ (fun y : X => blockFlow (Real.sqrt 2) (-t) (sndC y)) (flow t x) := by
    have hh : ContDiffAt ℝ ⊤ (blockFlow (Real.sqrt 2) (-t)) (sndC (flow t x)) := by
      simpa only [flow, sndC_pack] using contDiffAt_blockFlow_reverse (Real.sqrt 2) ht (sndC x)
    have hcomp := hh.comp (flow t x) contDiff_sndC.contDiffAt
    convert hcomp using 1 <;> rfl
  have hv : ContDiffAt ℝ ⊤ (fun y : X => Real.exp (-8 * -t) * y 4) (flow t x) := by fun_prop
  have hh := contDiff_pack.contDiffAt.comp (flow t x) (h₁.prodMk (h₂.prodMk hv))
  convert hh using 1 <;> rfl

lemma derivative_injective {t : ℝ} (ht : 0 ≤ t) (x : X) :
    Function.Injective (fderiv ℝ (flow t) x) := by
  have hf := (contDiff_flow ht).differentiable (by simp)
  have hg := (contDiffAt_flow_reverse ht x).differentiableAt (by simp)
  have hh := hg.hasFDerivAt.comp x (hf x).hasFDerivAt
  have heq : flow (-t) ∘ flow t = id := funext (flow_reverse ht)
  rw [heq] at hh
  have hlin := hh.unique (hasFDerivAt_id x)
  intro u v huv
  have hh' := congrArg (fun A : X →L[ℝ] X => A u) hlin
  have hh'' := congrArg (fun A : X →L[ℝ] X => A v) hlin
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hh' hh''
  rw [huv] at hh'
  exact hh'.symm.trans hh''

def system : C1DynamicalSystem 5 where
  U := univ
  open_U := isOpen_univ
  nonempty_U := ⟨0, mem_univ _⟩
  f := vectorField
  f_C1 := (contDiff_vectorField.of_le (by simp)).contDiffOn
  φ := flow
  initial := fun x _ => flow_zero x
  forward_invariant := fun _ _ _ _ => mem_univ _
  semigroup := fun t s ht hs x _ => (flow_comp ht hs x).symm
  continuous_flow := continuousOn_jointFlow
  flow_C1 := fun t ht => ((contDiff_flow ht).of_le (by simp)).contDiffOn
  solves_ODE := fun x _ t ht => (flow_solves_ODE ht x).hasDerivWithinAt
  derivative_injective := fun t ht x _ => derivative_injective ht.le x

lemma system_globalAttractor : system.GlobalAttractor K := by
  refine ⟨⟨nonempty_K, isCompact_K, subset_univ _, ?_⟩, ?_⟩
  · intro t ht
    exact flow_image_K ht
  · intro B _ hB
    exact uniformlyAttracts_K B hB

end PolynomialCounterexample
end Eden
