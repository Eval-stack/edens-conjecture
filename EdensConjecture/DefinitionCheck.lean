import EdensConjecture.MainProof.Volume

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

/-!
# Agreement of the three local dimension constructions

The convergence condition is pointwise in the initial state and in each of
the n singular-value indices. It asserts finite real limits, rather than
merely the existence of upper exponents.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace Eden.DefinitionCheck

/-- Every normalized logarithmic singular value has a finite real limit. -/
def SingularValueRatesConverge {n : ℕ} (D : C1DynamicalSystem n)
    (u : PhaseSpace n) (rates : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i < n →
    Tendsto (fun t : ℝ => D.finiteTimeLE t u i) atTop (𝓝 (rates i))

lemma exponentSum_congr {n k : ℕ} {a b : ℕ → ℝ}
    (hk : k ≤ n) (h : ∀ i < n, a i = b i) :
    exponentSum a k = exponentSum b k := by
  apply Finset.sum_congr rfl
  intro i hi
  exact h i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)

lemma kaplanYorkeDimension_congr {n : ℕ} {a b : ℕ → ℝ}
    (h : ∀ i < n, a i = b i) :
    kaplanYorkeDimension n a = kaplanYorkeDimension n b := by
  have hi : kaplanYorkeIndex n a = kaplanYorkeIndex n b := by
    unfold kaplanYorkeIndex
    congr 1
    ext j
    by_cases hj : j ≤ n
    · simp only [Set.mem_setOf_eq, hj, true_and]
      rw [exponentSum_congr hj h]
    · simp [hj]
  unfold kaplanYorkeDimension
  rw [hi]
  by_cases hj : kaplanYorkeIndex n b = n
  · simp [hj]
  · rw [if_neg hj, if_neg hj,
      exponentSum_congr (PolynomialCounterexample.kaplanYorkeIndex_le n b) h,
      h _ (lt_of_le_of_ne (PolynomialCounterexample.kaplanYorkeIndex_le n b) hj)]

lemma upperLE_eq_of_convergence {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ}
    (h : SingularValueRatesConverge D u rates) {i : ℕ} (hi : i < n) :
    D.upperLE u i = rates i :=
  (h i hi).limsup_eq

lemma exponentSum_tendsto {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ}
    (h : SingularValueRatesConverge D u rates) {k : ℕ} (hk : k ≤ n) :
    Tendsto (fun t : ℝ => exponentSum (D.finiteTimeLE t u) k)
      atTop (𝓝 (exponentSum rates k)) := by
  exact tendsto_finsetSum _ (fun i hi => h i
    (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))

lemma cumulativeUpperLE_eq_of_convergence {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ}
    (h : SingularValueRatesConverge D u rates) {k : ℕ} (hk : k ≤ n) :
    D.cumulativeUpperLE u k = exponentSum rates k := by
  unfold C1DynamicalSystem.cumulativeUpperLE
  split_ifs with hk0
  · subst k
    simp [exponentSum]
  · exact (exponentSum_tendsto h hk).limsup_eq

lemma relativeUpperLE_eq_of_convergence {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ}
    (h : SingularValueRatesConverge D u rates) {i : ℕ} (hi : i < n) :
    D.relativeUpperLE u i = rates i := by
  rw [C1DynamicalSystem.relativeUpperLE,
    cumulativeUpperLE_eq_of_convergence h hi,
    cumulativeUpperLE_eq_of_convergence h hi.le]
  simp [exponentSum, Finset.sum_range_succ]

/-- Convergence alone identifies the two Kaplan--Yorke constructions. -/
theorem kaplanYorke_constructions_agree {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ}
    (h : SingularValueRatesConverge D u rates) :
    kaplanYorkeDimensionOfUpperLE D u = kaplanYorkeDimension n rates ∧
    kaplanYorkeDimensionOfRelativeUpperLE D u = kaplanYorkeDimension n rates := by
  constructor
  · exact kaplanYorkeDimension_congr (fun _ hi => upperLE_eq_of_convergence h hi)
  · exact kaplanYorkeDimension_congr (fun _ hi => relativeUpperLE_eq_of_convergence h hi)

/-- The interpolation of limiting exponent sums corresponding to ω_d. -/
def interpolatedExponent (rates : ℕ → ℝ) (d : ℝ) : ℝ :=
  exponentSum rates ⌊d⌋₊ + (d - (⌊d⌋₊ : ℝ)) * rates ⌊d⌋₊

lemma singularValues_pos {n : ℕ} (D : C1DynamicalSystem n)
    {u : PhaseSpace n} (hu : u ∈ D.U) {t : ℝ} (ht : 0 < t)
    {i : ℕ} (hi : i < n) : 0 < D.σ t u i := by
  apply (((fderiv ℝ (D.φ t) u).toLinearMap.injective_iff_forall_lt_finrank_singularValues_pos).mp
    (D.derivative_injective t ht u hu)) i
  simpa [PhaseSpace] using hi

lemma singularValueGrowth_eq {n : ℕ} (D : C1DynamicalSystem n)
    {u : PhaseSpace n} (hu : u ∈ D.U) {t d : ℝ} (ht : 0 < t)
    (hd : d ∈ Icc (0 : ℝ) (n : ℝ)) :
    D.singularValueGrowth d t u =
      ((if d = (⌊d⌋₊ : ℝ) then exponentSum (D.finiteTimeLE t u) ⌊d⌋₊
        else interpolatedExponent (D.finiteTimeLE t u) d : ℝ) : EReal) := by
  have hk : ⌊d⌋₊ ≤ n := Nat.floor_le_of_le hd.2
  have hp : 0 < ∏ i ∈ Finset.range ⌊d⌋₊, D.σ t u i :=
    Finset.prod_pos (fun i hi => singularValues_pos D hu ht
      (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
  have hlog : Real.log (∏ i ∈ Finset.range ⌊d⌋₊, D.σ t u i) / t =
      exponentSum (D.finiteTimeLE t u) ⌊d⌋₊ := by
    rw [Real.log_prod (fun i hi => (singularValues_pos D hu ht
      (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)).ne')]
    simp [exponentSum, C1DynamicalSystem.finiteTimeLE, Finset.sum_div]
  by_cases hdeq : d = (⌊d⌋₊ : ℝ)
  · have hw : D.ω d t u = ∏ i ∈ Finset.range ⌊d⌋₊, D.σ t u i := by
      simp only [C1DynamicalSystem.ω, singularValueFunction, C1DynamicalSystem.σ, if_pos hdeq]
    rw [C1DynamicalSystem.singularValueGrowth, hw, if_neg hp.ne', if_pos hdeq,
      ← EReal.coe_mul]
    congr 1
    simpa [div_eq_mul_inv, mul_comm] using hlog
  · have hkn : ⌊d⌋₊ < n := by
      by_contra hkn
      have heq : ⌊d⌋₊ = n := by omega
      exact hdeq (le_antisymm (by simpa only [heq] using hd.2) (Nat.floor_le hd.1))
    have hs := singularValues_pos D hu ht hkn
    have hw : D.ω d t u =
        (∏ i ∈ Finset.range ⌊d⌋₊, D.σ t u i) *
          Real.rpow (D.σ t u ⌊d⌋₊) (d - (⌊d⌋₊ : ℝ)) := by
      simp only [C1DynamicalSystem.ω, singularValueFunction, C1DynamicalSystem.σ, if_neg hdeq]
    have hpow : 0 < Real.rpow (D.σ t u ⌊d⌋₊) (d - (⌊d⌋₊ : ℝ)) :=
      Real.rpow_pos_of_pos hs _
    have hlogpow : Real.log (Real.rpow (D.σ t u ⌊d⌋₊) (d - (⌊d⌋₊ : ℝ))) =
        (d - (⌊d⌋₊ : ℝ)) * Real.log (D.σ t u ⌊d⌋₊) :=
      Real.log_rpow hs _
    rw [C1DynamicalSystem.singularValueGrowth, hw,
      if_neg (mul_pos hp hpow).ne', if_neg hdeq,
      Real.log_mul hp.ne' hpow.ne', hlogpow,
      ← EReal.coe_mul]
    congr 1
    unfold interpolatedExponent
    rw [← hlog]
    unfold C1DynamicalSystem.finiteTimeLE
    ring

lemma singularValueGrowth_eq_interpolated {n : ℕ} (D : C1DynamicalSystem n)
    {u : PhaseSpace n} (hu : u ∈ D.U) {t d : ℝ} (ht : 0 < t)
    (hd : d ∈ Icc (0 : ℝ) (n : ℝ)) :
    D.singularValueGrowth d t u = (interpolatedExponent (D.finiteTimeLE t u) d : EReal) := by
  rw [singularValueGrowth_eq D hu ht hd]
  split_ifs with hdeq
  · simp only [interpolatedExponent, sub_eq_zero.mpr hdeq, zero_mul, add_zero]
  · rfl

/-- Convergence of the individual rates gives the interpolated limiting
growth rate of every singular-value function, including integer endpoints. -/
theorem singularValueGrowth_tendsto {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ} (hu : u ∈ D.U)
    (h : SingularValueRatesConverge D u rates) {d : ℝ}
    (hd : d ∈ Icc (0 : ℝ) (n : ℝ)) :
    Tendsto (fun t : ℝ => D.singularValueGrowth d t u) atTop
      (𝓝 (interpolatedExponent rates d : EReal)) := by
  have hk : ⌊d⌋₊ ≤ n := Nat.floor_le_of_le hd.2
  by_cases hdeq : d = (⌊d⌋₊ : ℝ)
  · have hs := exponentSum_tendsto h hk
    have he : interpolatedExponent rates d = exponentSum rates ⌊d⌋₊ := by
      simp only [interpolatedExponent, sub_eq_zero.mpr hdeq, zero_mul, add_zero]
    rw [he]
    apply (continuous_coe_real_ereal.continuousAt.tendsto.comp hs).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [singularValueGrowth_eq D hu ht hd, if_pos hdeq]
    rfl
  · have hkn : ⌊d⌋₊ < n := by
      by_contra hkn
      have heq : ⌊d⌋₊ = n := by omega
      exact hdeq (le_antisymm (by simpa only [heq] using hd.2) (Nat.floor_le hd.1))
    have hs := (exponentSum_tendsto h hk).add ((h _ hkn).const_mul
      (d - (⌊d⌋₊ : ℝ)))
    apply (continuous_coe_real_ereal.continuousAt.tendsto.comp hs).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [singularValueGrowth_eq D hu ht hd, if_neg hdeq]
    rfl

lemma limiting_rates_antitone {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ}
    (hu : u ∈ D.U) (h : SingularValueRatesConverge D u rates) :
    ∀ i j : ℕ, i ≤ j → j < n → rates j ≤ rates i := by
  intro i j hij hj
  apply le_of_tendsto_of_tendsto (h j hj) (h i (hij.trans_lt hj))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  apply div_le_div_of_nonneg_right _ ht.le
  exact Real.log_le_log (singularValues_pos D hu ht hj)
    ((fderiv ℝ (D.φ t) u).toLinearMap.singularValues_antitone hij)

lemma nonnegative_prefix_sums {n j : ℕ} {rates : ℕ → ℝ}
    (hmono : ∀ i l : ℕ, i ≤ l → l < n → rates l ≤ rates i)
    (hj : j ≤ n) (hs : 0 ≤ exponentSum rates j) :
    ∀ k ≤ j, 0 ≤ exponentSum rates k := by
  intro k hk
  by_contra hbad
  have hneg : exponentSum rates k < 0 := lt_of_not_ge hbad
  have hk0 : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    simp [this, exponentSum] at hneg
  have hr : rates (k - 1) < 0 := by
    by_contra hh
    have hnonneg : 0 ≤ exponentSum rates k := by
      apply Finset.sum_nonneg
      intro i hi
      exact (le_of_not_gt hh).trans
        (hmono i (k - 1) (by have := Finset.mem_range.mp hi; omega) (by omega))
    exact (not_lt_of_ge hnonneg) hneg
  have htail : ∀ l, k ≤ l → l ≤ n → exponentSum rates l < 0 := by
    intro l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ => hneg
    | succ l hkl ih =>
      intro hln
      rw [exponentSum, Finset.sum_range_succ]
      exact add_neg (ih (by omega))
        ((hmono (k - 1) l (by omega) (by omega)).trans_lt hr)
  exact (not_lt_of_ge hs) (htail j hk hj)

lemma interpolatedExponent_neg_iff {n : ℕ} {rates : ℕ → ℝ}
    (hmono : ∀ i l : ℕ, i ≤ l → l < n → rates l ≤ rates i)
    {d : ℝ} (hd : d ∈ Icc (0 : ℝ) (n : ℝ)) :
    interpolatedExponent rates d < 0 ↔ kaplanYorkeDimension n rates < d := by
  let j := kaplanYorkeIndex n rates
  let k := ⌊d⌋₊
  have hj : j ≤ n := PolynomialCounterexample.kaplanYorkeIndex_le n rates
  have hSj : 0 ≤ exponentSum rates j := PolynomialCounterexample.kaplanYorkeIndex_mem n rates
  have hprefix := nonnegative_prefix_sums hmono hj hSj
  have hnegative : ∀ l, j < l → l ≤ n → exponentSum rates l < 0 := by
    intro l hjl hln
    by_contra hh
    have hle : l ≤ j := le_csSup ⟨n, fun _ h => h.1⟩ ⟨hln, le_of_not_gt hh⟩
    omega
  have hk : k ≤ n := Nat.floor_le_of_le hd.2
  have hkd : (k : ℝ) ≤ d := Nat.floor_le hd.1
  have hdk : d < (k : ℝ) + 1 := Nat.lt_floor_add_one d
  have hp : interpolatedExponent rates d =
      exponentSum rates k + (d - (k : ℝ)) * rates k := rfl
  have hconvex (hkn : k < n) : interpolatedExponent rates d =
      ((k : ℝ) + 1 - d) * exponentSum rates k +
        (d - (k : ℝ)) * exponentSum rates (k + 1) := by
    rw [hp]
    simp only [exponentSum, Finset.sum_range_succ]
    ring
  by_cases hjn : j = n
  · have hc : kaplanYorkeDimension n rates = (n : ℝ) := by
      change (if j = n then (n : ℝ) else
        (j : ℝ) + exponentSum rates j / |rates j|) = n
      rw [if_pos hjn]
    rw [hc]
    have hP : 0 ≤ interpolatedExponent rates d := by
      by_cases hkn : k < n
      · rw [hconvex hkn]
        exact add_nonneg (mul_nonneg (by linarith) (hprefix k (by omega)))
          (mul_nonneg (by linarith) (hprefix (k + 1) (by omega)))
      · have hkn : k = n := by omega
        have hdn : d = (k : ℝ) := le_antisymm (by simpa only [hkn] using hd.2) hkd
        rw [hp, hdn]
        simpa using hprefix k (by omega)
    exact iff_of_false (not_lt_of_ge hP) (not_lt_of_ge hd.2)
  · have hjn' : j < n := lt_of_le_of_ne hj hjn
    have hnext : exponentSum rates j + rates j < 0 := by
      have := hnegative (j + 1) (by omega) (by omega)
      simpa [exponentSum, Finset.sum_range_succ] using this
    have hr : rates j < 0 := by linarith
    have hc : kaplanYorkeDimension n rates =
        (j : ℝ) + exponentSum rates j / (-rates j) := by
      change (if j = n then (n : ℝ) else
        (j : ℝ) + exponentSum rates j / |rates j|) = _
      rw [if_neg hjn, abs_of_neg hr]
    have hcj : (j : ℝ) ≤ kaplanYorkeDimension n rates := by
      rw [hc]
      exact le_add_of_nonneg_right (div_nonneg hSj (by linarith))
    have hcj1 : kaplanYorkeDimension n rates < (j : ℝ) + 1 := by
      rw [hc]
      have : exponentSum rates j / (-rates j) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      linarith
    rcases lt_trichotomy k j with hkj | hkj | hjk
    · have hP : 0 ≤ interpolatedExponent rates d := by
        rw [hconvex (by omega)]
        exact add_nonneg (mul_nonneg (by linarith) (hprefix k (by omega)))
          (mul_nonneg (by linarith) (hprefix (k + 1) (by omega)))
      have hdc : d ≤ kaplanYorkeDimension n rates := by
        have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
        linarith
      exact iff_of_false (not_lt_of_ge hP) (not_lt_of_ge hdc)
    · have he : interpolatedExponent rates d =
          (-rates j) * (kaplanYorkeDimension n rates - d) := by
        rw [hp, hkj, hc]
        field_simp [hr.ne]
        ring
      rw [he]
      constructor
      · intro hh
        by_contra hdc
        exact (not_lt_of_ge (mul_nonneg (by linarith : 0 ≤ -rates j)
          (sub_nonneg.mpr (le_of_not_gt hdc)))) hh
      · intro hcd
        exact mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr hcd)
    · have hP : interpolatedExponent rates d < 0 := by
        by_cases hkn : k < n
        · rw [hp]
          have hrk : rates k < 0 := (hmono j k (by omega) hkn).trans_lt hr
          exact add_neg_of_neg_of_nonpos (hnegative k hjk hk)
            (mul_nonpos_of_nonneg_of_nonpos (by linarith) hrk.le)
        · have hkn : k = n := by omega
          have hdn : d = (k : ℝ) := le_antisymm (by simpa only [hkn] using hd.2) hkd
          rw [hp, hdn]
          simpa using hnegative k hjk hk
      have hcd : kaplanYorkeDimension n rates < d := by
        have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
        linarith
      exact iff_of_true hP hcd

/-- Finite real convergence of every singular-value growth rate suffices
for all three definitions to agree, with the endpoint value n for an empty
contraction set. No convergence of finite-time dimensions is assumed. -/
theorem all_three_definitions_agree {n : ℕ} {D : C1DynamicalSystem n}
    {u : PhaseSpace n} {rates : ℕ → ℝ} (hu : u ∈ D.U)
    (h : SingularValueRatesConverge D u rates) :
    localLyapunovDimension D u = (kaplanYorkeDimension n rates : EReal) ∧
    kaplanYorkeDimensionOfUpperLE D u = kaplanYorkeDimension n rates ∧
    kaplanYorkeDimensionOfRelativeUpperLE D u = kaplanYorkeDimension n rates := by
  have hmono := limiting_rates_antitone hu h
  have hg (d : ℝ) (hd : d ∈ Icc (0 : ℝ) (n : ℝ)) :
      D.upperSingularValueGrowth d u < 0 ↔ kaplanYorkeDimension n rates < d := by
    rw [C1DynamicalSystem.upperSingularValueGrowth,
      (singularValueGrowth_tendsto hu h hd).limsup_eq]
    exact EReal.coe_lt_coe_iff.trans (interpolatedExponent_neg_iff hmono hd)
  have hc : kaplanYorkeDimension n rates ≤ n :=
    PolynomialCounterexample.kaplanYorkeDimension_le n rates
  refine ⟨?_, kaplanYorke_constructions_agree h⟩
  apply le_antisymm
  · by_cases hcn : kaplanYorkeDimension n rates = n
    · rw [hcn]
      exact sInf_le (Set.mem_insert _ _)
    · have hcn : kaplanYorkeDimension n rates < n := lt_of_le_of_ne hc hcn
      have hlim : Tendsto (fun d : ℝ => (d : EReal))
          (𝓝[>] (kaplanYorkeDimension n rates)) (𝓝 (kaplanYorkeDimension n rates : EReal)) :=
        tendsto_nhdsWithin_of_tendsto_nhds continuous_coe_real_ereal.continuousAt
      apply ge_of_tendsto hlim
      have hn : ∀ᶠ d : ℝ in 𝓝[>] (kaplanYorkeDimension n rates), d < n :=
        (eventually_lt_nhds hcn).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hn] with d hd hn
      have hc0 : 0 ≤ kaplanYorkeDimension n rates := by
        dsimp only [kaplanYorkeDimension]
        split_ifs with hj
        · positivity
        · exact add_nonneg (Nat.cast_nonneg _) (div_nonneg
            (PolynomialCounterexample.kaplanYorkeIndex_mem n rates) (abs_nonneg _))
      exact sInf_le (Set.mem_insert_of_mem _ ⟨d, ⟨hc0.trans hd.le, hn.le⟩, rfl,
        (hg d ⟨hc0.trans hd.le, hn.le⟩).mpr hd⟩)
  · apply le_sInf
    intro a ha
    rcases ha with rfl | ⟨d, hd, rfl, hneg⟩
    · exact_mod_cast hc
    · exact_mod_cast ((hg d hd).mp hneg).le

lemma finiteTime_dimension_nonneg {n : ℕ} (D : C1DynamicalSystem n)
    (t : ℝ) (u : PhaseSpace n) : 0 ≤ finiteTimeLyapunovDimensionAt D t u :=
  Real.sSup_nonneg (fun _ hd => hd.1.1)

lemma finiteTime_dimension_le_of_constant_rates {n : ℕ} (D : C1DynamicalSystem n)
    {u : PhaseSpace n} (hu : u ∈ D.U) {t : ℝ} (ht : 0 < t)
    (rates : ℕ → ℝ) (hconst : D.finiteTimeLE t u = rates)
    (hmono : ∀ i l : ℕ, i ≤ l → l < n → rates l ≤ rates i)
    (hc0 : 0 ≤ kaplanYorkeDimension n rates) :
    finiteTimeLyapunovDimensionAt D t u ≤ kaplanYorkeDimension n rates := by
  apply Real.sSup_le _ hc0
  rintro d ⟨hd, hω⟩
  by_contra hdc
  have hP : interpolatedExponent rates d < 0 :=
    (interpolatedExponent_neg_iff hmono hd).mpr (lt_of_not_ge hdc)
  have hneg : D.singularValueGrowth d t u < 0 := by
    rw [singularValueGrowth_eq_interpolated D hu ht hd, hconst]
    exact_mod_cast hP
  have hpos : (0 : EReal) < D.singularValueGrowth d t u := by
    rw [C1DynamicalSystem.singularValueGrowth,
      if_neg (ne_of_gt (lt_trans zero_lt_one hω)), ← EReal.coe_mul]
    exact_mod_cast (mul_pos (inv_pos.mpr ht) (Real.log_pos hω))
  exact (not_lt_of_ge hpos.le) hneg

namespace Counterexample

open PolynomialCounterexample

lemma sorted_selection_tendsto (a : ℝ → Fin 5 → ℝ) (limits : Fin 5 → ℝ)
    (p : ℝ → Equiv.Perm (Fin 5))
    (hlim : ∀ i, Tendsto (fun t => a t i) atTop (𝓝 (limits i)))
    (hsort : ∀ᶠ t in atTop, Antitone (a t ∘ p t)) (i : Fin 5) :
    Tendsto (fun t => a t (p t i)) atTop (𝓝 (decreasingValues limits i)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hperm : ∀ q : Equiv.Perm (Fin 5), ∀ᶠ t in atTop,
      Antitone (a t ∘ q) → dist (a t (q i)) (decreasingValues limits i) < ε := by
    intro q
    by_cases hq : Antitone (limits ∘ q)
    · have he := congrFun (Tuple.unique_antitone hq (decreasingValues_antitone limits)) i
      have he : limits (q i) = decreasingValues limits i := he
      rw [← he]
      exact ((Metric.tendsto_nhds.mp (hlim (q i))) ε hε).mono (fun _ h _ => h)
    · change ¬ ∀ x y : Fin 5, x ≤ y → limits (q y) ≤ limits (q x) at hq
      push_neg at hq
      obtain ⟨j, k, hjk, hlt⟩ := hq
      filter_upwards [(hlim (q j)).eventually_lt (hlim (q k)) hlt] with t ht hsorted
      exact (not_lt_of_ge (hsorted hjk) ht).elim
  filter_upwards [Filter.eventually_all.mpr hperm, hsort] with t ht hsorted
  exact ht (p t) hsorted

lemma normalizedLog_tendsto_zero {f : ℝ → ℝ} {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) (ha : a ≠ 0) :
    Tendsto (fun t => Real.log (f t) / t) atTop (𝓝 (0 : ℝ)) :=
  (h.log ha).div_atTop tendsto_id

lemma radialDenominator_tendsto (q : ℝ) :
    Tendsto (fun t => radialDenominator t (q - 1)) atTop (𝓝 ((q - 1) ^ 2)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-4 * t)) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (by norm_num : (-4 : ℝ) < 0)).mpr tendsto_id)
  simpa [radialDenominator] using
    (tendsto_const_nhds.add (he.const_mul (1 - (q - 1) ^ 2)))

lemma radialJacobian_rate {q : ℝ} (hq : q ≠ 1) :
    Tendsto (fun t => Real.log (radialJacobian t q) / t) atTop (𝓝 (-4 : ℝ)) := by
  have hs := (radialDenominator_tendsto q).sqrt
  have hs0 : Real.sqrt ((q - 1) ^ 2) ≠ 0 := by
    rw [Real.sqrt_sq_eq_abs]
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hq)
  have hz := normalizedLog_tendsto_zero hs hs0
  have hh := (tendsto_const_nhds (x := (-4 : ℝ))).sub (hz.const_mul 3)
  apply (show Tendsto (fun t : ℝ => -4 - 3 * (Real.log
      (Real.sqrt (radialDenominator t (q - 1))) / t)) atTop (𝓝 (-4 : ℝ)) by
    simpa using hh).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [radialJacobian, Real.log_div (Real.exp_pos _).ne'
    (pow_ne_zero 3 (Real.sqrt_pos.mpr (radialDenominator_pos ht.le _)).ne'),
    Real.log_exp, Real.log_pow]
  field_simp
  ring

lemma positiveScale_rate_below {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    Tendsto (fun t => Real.log (positiveScale t q) / t) atTop (𝓝 (-2 : ℝ)) := by
  let c : ℝ → ℝ := fun t => (2 - q) /
    (Real.sqrt (radialDenominator t (q - 1)) *
      (Real.sqrt (radialDenominator t (q - 1)) - (q - 1)))
  let L : ℝ := (2 - q) / ((1 - q) * (2 * (1 - q)))
  have hs : Tendsto (fun t => Real.sqrt (radialDenominator t (q - 1)))
      atTop (𝓝 (1 - q)) := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_neg (by linarith : q - 1 < 0)] using
      (radialDenominator_tendsto q).sqrt
  have hL : 0 < L := div_pos (by linarith)
    (mul_pos (by linarith) (by linarith))
  have hc : Tendsto c atTop (𝓝 L) := by
    have hh := (tendsto_const_nhds (x := 2 - q)).div (hs.mul (hs.sub_const (q - 1)))
      (show (1 - q) * ((1 - q) - (q - 1)) ≠ 0 by nlinarith)
    convert hh using 1 <;> dsimp [c, L] <;> congr 1 <;> ring
  have hz := normalizedLog_tendsto_zero hc hL.ne'
  have hh : Tendsto (fun t => (Real.log (c t) / t - 4) / 2)
      atTop (𝓝 (-2 : ℝ)) := by
    convert (hz.sub_const 4).div_const 2 using 1 <;> norm_num
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hcp : 0 < c t := by
    dsimp [c]
    exact div_pos (by linarith)
      (mul_pos (Real.sqrt_pos.mpr (radialDenominator_pos ht.le _))
        (by have := Real.sqrt_nonneg (radialDenominator t (q - 1)); linarith))
  have he : positiveScale t q = Real.sqrt (c t * Real.exp (-4 * t)) := by
    unfold positiveScale
    have hreg := regularScaleSq_mul ht.le hq1
    rw [← hreg, mul_div_cancel_right₀ _ hq.ne']
    congr 1
    dsimp [regularScaleSq, c]
    ring
  rw [he, Real.log_sqrt (mul_pos hcp (Real.exp_pos _)).le,
    Real.log_mul hcp.ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

lemma positiveScale_rate_above {q : ℝ} (hq : 1 < q) :
    Tendsto (fun t => Real.log (positiveScale t q) / t) atTop (𝓝 (0 : ℝ)) := by
  have hs : Tendsto (fun t => Real.sqrt (radialDenominator t (q - 1)))
      atTop (𝓝 (q - 1)) := by
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith : 0 < q - 1)] using
      (radialDenominator_tendsto q).sqrt
  have hr : Tendsto (fun t => squaredRadius t q) atTop (𝓝 (2 : ℝ)) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.div hs (by linarith : q - 1 ≠ 0)) using 1
    · rfl
    · rw [div_self (by linarith : q - 1 ≠ 0)]
      norm_num
  apply normalizedLog_tendsto_zero (hr.div_const q |>.sqrt)
  exact (Real.sqrt_pos.mpr (div_pos (by norm_num) (by linarith))).ne'

/-- Both unsorted block singular-value growth rates converge at every radius. -/
lemma factors_rates_converge {q : ℝ} (hq : 0 ≤ q) :
    ∃ r s : ℝ,
      Tendsto (fun t => Real.log (radialFactor t q) / t) atTop (𝓝 r) ∧
      Tendsto (fun t => Real.log (tangentialFactor t q) / t) atTop (𝓝 s) := by
  by_cases hq0 : q = 0
  · subst q
    refine ⟨-2, -2, ?_, ?_⟩ <;> apply tendsto_const_nhds.congr' <;>
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht <;>
      simp [radialFactor, tangentialFactor, Real.log_exp] <;> field_simp <;> ring
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  by_cases hq1 : q = 1
  · subst q
    refine ⟨2, 0, ?_, ?_⟩
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have he : radialJacobian t 1 = Real.exp (2 * t) :=
        (hasDerivAt_squaredRadius_initial ht.le 1).unique (hasDerivAt_squaredRadius_one ht.le)
      simp [radialFactor, positiveScale, squaredRadius_at_one, he, Real.log_exp, ht.ne']
    · simp [tangentialFactor, positiveScale, squaredRadius_at_one]
  have hs : ∃ s : ℝ, Tendsto (fun t => Real.log (positiveScale t q) / t) atTop (𝓝 s) := by
    rcases lt_or_gt_of_ne hq1 with hlt | hgt
    · exact ⟨-2, positiveScale_rate_below hqp hlt⟩
    · exact ⟨0, positiveScale_rate_above hgt⟩
  obtain ⟨s, hs⟩ := hs
  refine ⟨-4 - s, s, ?_, ?_⟩
  · apply ((radialJacobian_rate hq1).sub hs).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [radialFactor, if_neg hq0, Real.log_div (radialJacobian_pos ht.le _).ne'
      (positiveScale_pos ht.le hqp).ne']
    ring
  · simpa [tangentialFactor, hq0] using hs

/-- The convergence condition holds at every point of the global attractor,
including trajectories whose radii are not equilibria. -/
theorem global_attractor_rates_converge {x : X} (hx : x ∈ K) :
    ∃ rates : ℕ → ℝ, SingularValueRatesConverge system x rates := by
  obtain ⟨r, s, hr, hs⟩ := factors_rates_converge (q₁_nonneg x)
  obtain ⟨r', s', hr', hs'⟩ := factors_rates_converge (q₂_nonneg x)
  let limits : Fin 5 → ℝ := ![r, s, r', s', -8]
  let a : ℝ → Fin 5 → ℝ := fun t i =>
    Real.log (fullDiagonal t (q₁ x) (q₂ x) i) / t
  let p : ℝ → Equiv.Perm (Fin 5) := fun t =>
    decreasingPermutation (fullDiagonal t (q₁ x) (q₂ x))
  have hlim : ∀ i, Tendsto (fun t => a t i) atTop (𝓝 (limits i)) := by
    intro i
    fin_cases i
    · exact hr
    · exact hs
    · exact hr'
    · exact hs'
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      simp [a, fullDiagonal, limits, Real.log_exp] <;> field_simp <;> ring
  have hsort : ∀ᶠ t in atTop, Antitone (a t ∘ p t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    intro i j hij
    apply div_le_div_of_nonneg_right _ ht.le
    apply Real.log_le_log
      ((Real.exp_pos _).trans_le (fullDiagonal_bounds ht.le hx (p t j)).1)
    exact decreasingValues_antitone _ hij
  refine ⟨fun i => if hi : i < 5 then decreasingValues limits ⟨i, hi⟩ else 0, ?_⟩
  intro i hi
  simp only [dif_pos hi]
  apply (sorted_selection_tendsto a limits p hlim hsort ⟨i, hi⟩).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [C1DynamicalSystem.finiteTimeLE, flow_singularValues_decreasing ht.le hx ⟨i, hi⟩]
  rfl

/-- All three local dimension definitions agree throughout the global attractor. -/
theorem global_attractor_definitions_agree {x : X} (hx : x ∈ K) :
    localLyapunovDimension system x = (kaplanYorkeDimensionOfUpperLE system x : EReal) ∧
    kaplanYorkeDimensionOfUpperLE system x = kaplanYorkeDimensionOfRelativeUpperLE system x := by
  obtain ⟨rates, h⟩ := global_attractor_rates_converge hx
  obtain ⟨hcanonical, hupper, hrelative⟩ := all_three_definitions_agree
    (show x ∈ system.U from Set.mem_univ _) h
  exact ⟨hcanonical.trans (congrArg (fun r : ℝ => (r : EReal)) hupper.symm),
    hupper.trans hrelative.symm⟩

/-- Every singular-value growth rate on the irrational torus is constant
for positive time, which proves the requested finite real convergence. -/
theorem torus_rates_converge {x : X} (hx : x ∈ T) :
    SingularValueRatesConverge system x (PolynomialCounterexample.spectrum 2 2 0 0 (-8)) := by
  intro i hi
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (congrFun (torus_finiteTimeLE_all ht hx) i).symm

/-- Convergence at each equilibrium radial pair, including all stationary
and periodic candidates classified in the global construction. -/
theorem equilibrium_rates_converge (r s : RadialType) {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    SingularValueRatesConverge system (pack (r.point a) (s.point b) 0)
      (radialPairSpectrum r s).rates := by
  intro i hi
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (congrFun (equilibrium_finiteTimeLE_all r s ht ha hb) i).symm

theorem torus_total_rate_negative :
    exponentSum (PolynomialCounterexample.spectrum 2 2 0 0 (-8)) 5 < 0 := by
  norm_num [exponentSum, PolynomialCounterexample.spectrum, Finset.sum_range_succ]

theorem equilibrium_total_rate_negative (r s : RadialType) :
    exponentSum (radialPairSpectrum r s).rates 5 < 0 :=
  SpectrumType.sum_five_neg _

theorem torus_localLyapunovDimension {x : X} (hx : x ∈ T) :
    localLyapunovDimension system x = ((9 / 2 : ℝ) : EReal) := by
  rw [(all_three_definitions_agree (show x ∈ system.U from Set.mem_univ _)
    (torus_rates_converge hx)).1, spectrum_BB_dimension]

theorem equilibrium_localLyapunovDimension (r s : RadialType) {a b : ℂ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    localLyapunovDimension system (pack (r.point a) (s.point b) 0) =
      (kaplanYorkeDimension 5 (radialPairSpectrum r s).rates : EReal) :=
  (all_three_definitions_agree (show _ ∈ system.U from Set.mem_univ _)
    (equilibrium_rates_converge r s ha hb)).1

theorem recurrent_localLyapunovDimension_le_three {x : X}
    (hx : StationarySolution flow x ∨ PeriodicSolution flow x) :
    localLyapunovDimension system x ≤ (3 : EReal) := by
  have hclass : (q₁ x = 0 ∨ q₁ x = 1 ∨ q₁ x = 2) ∧
      (q₂ x = 0 ∨ q₂ x = 1 ∨ q₂ x = 2) ∧ (fstC x = 0 ∨ sndC x = 0) ∧ x 4 = 0 := by
    rcases hx with hx | hx
    · have hz := (stationary_iff_zero x).mp hx
      subst x
      simp [q₁, q₂, fstC, sndC]
    · exact periodic_candidate_classification hx
  obtain ⟨r, a, ha, hxa, hra⟩ := exists_radialType (fstC x)
    (by rw [norm_fstC_sq]; exact hclass.1)
  obtain ⟨s, b, hb, hxb, hsb⟩ := exists_radialType (sndC x)
    (by rw [norm_sndC_sq]; exact hclass.2.1)
  have hrs : r = .zero ∨ s = .zero := hclass.2.2.1.imp hra.mp hsb.mp
  have heq : x = pack (r.point a) (s.point b) 0 := by
    rw [← hxa, ← hxb, ← hclass.2.2.2]
    exact (pack_coordinates x).symm
  rw [heq, equilibrium_localLyapunovDimension r s ha hb]
  rcases hrs with rfl | rfl
  · cases s <;> simp only [radialPairSpectrum, SpectrumType.rates,
      spectrum_AA_dimension, spectrum_AB_dimension, spectrum_AC_dimension] <;>
      apply EReal.coe_le_coe_iff.mpr <;> norm_num
  · cases r <;> simp only [radialPairSpectrum, SpectrumType.rates,
      spectrum_AA_dimension, spectrum_AB_dimension, spectrum_AC_dimension] <;>
      apply EReal.coe_le_coe_iff.mpr <;> norm_num

theorem no_periodic_canonical_attainment :
    ¬ ∃ x ∈ K, (StationarySolution system.φ x ∨ PeriodicSolution system.φ x) ∧
      Orbit system.φ x ⊆ K ∧
      localLyapunovDimension system x = supremumLocalLyapunovDimension system K := by
  rintro ⟨x, _, hrec, _, heq⟩
  obtain ⟨y, hy⟩ := nonempty_T
  have hle : localLyapunovDimension system y ≤ supremumLocalLyapunovDimension system K :=
    le_sSup (Set.mem_image_of_mem _ (T_subset_K hy))
  rw [← heq, torus_localLyapunovDimension hy] at hle
  have hsmall := recurrent_localLyapunovDimension_le_three hrec
  have hbad := hle.trans hsmall
  have hbad' : (9 : ℝ) / 2 ≤ 3 := EReal.coe_le_coe_iff.mp hbad
  norm_num at hbad'

theorem global_refutation :
    ¬ (∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
      ∀ K : Set (PhaseSpace n), D.GlobalAttractor K →
        ∃ u ∈ K, (StationarySolution D.φ u ∨ PeriodicSolution D.φ u) ∧
          Orbit D.φ u ⊆ K ∧
          localLyapunovDimension D u = supremumLocalLyapunovDimension D K) := by
  intro h
  exact no_periodic_canonical_attainment (h 5 (by norm_num) system K system_globalAttractor)

lemma torus_set_dimension_le : lyapunovDimension system T ≤ (9 : ℝ) / 2 := by
  have hbound : BddBelow {a : ℝ | ∃ t : ℝ,
      0 < t ∧ a = finiteTimeLyapunovDimension system t T} := by
    refine ⟨0, ?_⟩
    rintro a ⟨t, _, rfl⟩
    apply Real.sSup_nonneg
    rintro _ ⟨x, _, rfl⟩
    exact finiteTime_dimension_nonneg system t x
  apply (csInf_le hbound ⟨1, by norm_num, rfl⟩).trans
  apply Real.sSup_le _ (by norm_num)
  rintro _ ⟨x, hx, rfl⟩
  have hh := finiteTime_dimension_le_of_constant_rates system
    (show x ∈ system.U from Set.mem_univ _) (by norm_num : (0 : ℝ) < 1)
    (PolynomialCounterexample.spectrum 2 2 0 0 (-8)) (torus_finiteTimeLE_all (by norm_num) hx)
    (limiting_rates_antitone (show x ∈ system.U from Set.mem_univ _) (torus_rates_converge hx))
    (by rw [spectrum_BB_dimension]; norm_num)
  simpa only [spectrum_BB_dimension] using hh

theorem torus_critical_exists : ∃ x : X, CriticalPath system T x := by
  obtain ⟨x, hx⟩ := nonempty_T
  refine ⟨x, hx, ?_⟩
  rw [torus_localLyapunovDimension hx]
  exact_mod_cast torus_set_dimension_le

theorem question1_refutation :
    ¬ (∀ n : ℕ, 0 < n → ∀ D : C1DynamicalSystem n,
      ∀ K : Set (PhaseSpace n), D.CompactInvariantSet K →
        (∃ u : PhaseSpace n, CriticalPath D K u) →
        ∃ u : PhaseSpace n, CriticalPath D K u ∧
          (StationarySolution D.φ u ∨ PeriodicSolution D.φ u)) := by
  intro h
  obtain ⟨x, hx, hrec⟩ := h 5 (by norm_num) system T
    ⟨nonempty_T, isCompact_T, Set.subset_univ _, fun _ ht => flow_image_T ht⟩
    torus_critical_exists
  rcases hrec with hs | hp
  · exact no_stationary_on_T hx.1 hs
  · exact no_periodic_on_T hx.1 hp

end Counterexample
end Eden.DefinitionCheck
