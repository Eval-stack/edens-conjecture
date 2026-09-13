import EdensConjecture.MainProof.Thesis
import EdensConjecture.MainProof.Volume

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate
namespace Eden.PolynomialCounterexample

lemma global_s_bounds {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) {i : ℕ} (hi : i < 5) :
    Real.exp (-8 * t) ≤ globalThesisSetting.s (i + 1) t x ∧
      globalThesisSetting.s (i + 1) t x ≤ Real.exp (4 * t) := by
  rw [globalThesisSetting_s x (⟨i, hi⟩ : Fin 5)]
  exact flow_singularValues_bounds ht hx ⟨i, hi⟩

lemma global_w_bounds {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) {k : ℕ} (hk : k ≤ 5) :
    Real.exp (-8 * (k : ℝ) * t) ≤ globalThesisSetting.w k t x ∧
      globalThesisSetting.w k t x ≤ Real.exp (4 * (k : ℝ) * t) := by
  have hlo : (∏ _i ∈ Finset.range k, Real.exp (-8 * t)) ≤ globalThesisSetting.w k t x := by
    apply Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
    intro i hi
    exact (global_s_bounds ht hx (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)).1
  have hhi : globalThesisSetting.w k t x ≤ ∏ _i ∈ Finset.range k, Real.exp (4 * t) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact (Real.exp_pos _).le.trans (global_s_bounds ht hx (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)).1
    · intro i hi
      exact (global_s_bounds ht hx (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)).2
  simp only [Finset.prod_const, Finset.card_range, ← Real.exp_nat_mul] at hlo hhi
  constructor
  · convert hlo using 1 <;> congr 1 <;> ring
  · convert hhi using 1 <;> congr 1 <;> ring

lemma global_w_pos {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) {k : ℕ} (hk : k ≤ 5) :
    0 < globalThesisSetting.w k t x := (Real.exp_pos _).trans_le (global_w_bounds ht hx hk).1

def normalizedVolume (k : ℕ) (t : ℝ) (x : X) : ℝ := Real.log (globalThesisSetting.w k t x) / t

lemma normalizedVolume_bounds {t : ℝ} (ht : 0 < t) {x : X} (hx : x ∈ K) {k : ℕ} (hk : k ≤ 5) :
    -8 * (k : ℝ) ≤ normalizedVolume k t x ∧ normalizedVolume k t x ≤ 4 * (k : ℝ) := by
  obtain ⟨hlo, hhi⟩ := global_w_bounds ht.le hx hk
  have hl := Real.log_le_log (Real.exp_pos _) hlo
  have hh := Real.log_le_log (global_w_pos ht.le hx hk) hhi
  rw [Real.log_exp] at hl hh
  exact ⟨(le_div_iff₀ ht).mpr hl, (div_le_iff₀ ht).mpr hh⟩

lemma global_cumulative_eq_limsup {x : X} (hx : x ∈ K) {k : ℕ} (hk : k ≤ 5) :
    globalThesisSetting.cumulativeLocalExponent k x =
      limsup (fun t : ℝ => (normalizedVolume k t x : EReal)) atTop := by
  apply Filter.limsup_congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [ThesisSetting.extendedLog, if_neg (global_w_pos ht.le hx hk).ne', ← EReal.coe_mul]
  congr 1
  simp [normalizedVolume, div_eq_mul_inv, mul_comm]

lemma global_cumulative_bounds {x : X} (hx : x ∈ K) {k : ℕ} (hk : k ≤ 5) :
    ((-8 * (k : ℝ) : ℝ) : EReal) ≤ globalThesisSetting.cumulativeLocalExponent k x ∧
      globalThesisSetting.cumulativeLocalExponent k x ≤ ((4 * (k : ℝ) : ℝ) : EReal) := by
  rw [global_cumulative_eq_limsup hx hk]
  constructor
  · have hh := Filter.limsup_le_limsup (f := atTop)
      (u := fun _ : ℝ => ((-8 * (k : ℝ) : ℝ) : EReal))
      (v := fun t : ℝ => (normalizedVolume k t x : EReal))
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
          exact EReal.coe_le_coe (normalizedVolume_bounds ht hx hk).1)
    simpa using hh
  · apply Filter.limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact EReal.coe_le_coe (normalizedVolume_bounds ht hx hk).2

lemma global_cumulative_finite {x : X} (hx : x ∈ K) {k : ℕ} (hk : k ≤ 5) :
    globalThesisSetting.cumulativeLocalExponent k x ≠ ⊤ ∧
      globalThesisSetting.cumulativeLocalExponent k x ≠ ⊥ := by
  obtain ⟨hlo, hhi⟩ := global_cumulative_bounds hx hk
  exact ⟨(lt_of_le_of_lt hhi (EReal.coe_lt_top _)).ne,
    (lt_of_lt_of_le (EReal.bot_lt_coe _) hlo).ne'⟩

lemma global_cumulative_zero (x : X) : globalThesisSetting.cumulativeLocalExponent 0 x = 0 := by
  simp [ThesisSetting.cumulativeLocalExponent, ThesisSetting.w, ThesisSetting.extendedLog]

def globalCumulative (k : ℕ) (x : X) : ℝ := (globalThesisSetting.cumulativeLocalExponent k x).toReal
def globalMu (i : ℕ) (x : X) : ℝ := globalCumulative i x - globalCumulative (i - 1) x

lemma globalMu_sum (k : ℕ) (x : X) : ∑ i ∈ Finset.range k, globalMu (i + 1) x = globalCumulative k x := by
  induction k with
  | zero => simp [globalCumulative, global_cumulative_zero]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp [globalMu]

lemma global_realSpectrum : globalThesisSetting.RealLocalSpectrumThrough 4 globalMu := by
  intro x hx k hk
  rw [globalMu_sum]
  exact EReal.coe_toReal (global_cumulative_finite hx hk).1 (global_cumulative_finite hx hk).2

lemma normalizedVolume_five {t : ℝ} (ht : 0 < t) {x : X} (hx : x ∈ K) :
    normalizedVolume 5 t x = normalizedVolume 4 t x - 8 := by
  have hw : globalThesisSetting.w 5 t x = globalThesisSetting.w 4 t x * globalThesisSetting.s 5 t x := by
    exact Finset.prod_range_succ _ 4
  have hs : globalThesisSetting.s 5 t x = Real.exp (-8 * t) := by
    rw [globalThesisSetting_s x (⟨4, by decide⟩ : Fin 5), flow_fifth_singularValue ht.le hx]
  unfold normalizedVolume
  rw [hw, hs, Real.log_mul (global_w_pos ht.le hx (by norm_num)).ne' (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

lemma global_cumulative_five {x : X} (hx : x ∈ K) :
    globalThesisSetting.cumulativeLocalExponent 5 x = globalThesisSetting.cumulativeLocalExponent 4 x + ((-8 : ℝ) : EReal) := by
  rw [global_cumulative_eq_limsup hx (by norm_num), global_cumulative_eq_limsup hx (by norm_num)]
  have he : (fun t : ℝ => (normalizedVolume 5 t x : EReal)) =ᶠ[atTop]
      (fun t : ℝ => (normalizedVolume 4 t x : EReal) + ((-8 : ℝ) : EReal)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [normalizedVolume_five ht hx]
    simp [sub_eq_add_neg]
  rw [Filter.limsup_congr he]
  apply le_antisymm
  · simpa only [Pi.add_def, limsup_const] using EReal.limsup_add_le (u := fun t : ℝ => (normalizedVolume 4 t x : EReal))
      (v := fun _ : ℝ => ((-8 : ℝ) : EReal)) (f := atTop) (Or.inr (by simp)) (Or.inr (by simp))
  · simpa only [Pi.add_def, liminf_const] using (EReal.le_limsup_add (u := fun t : ℝ => (normalizedVolume 4 t x : EReal))
      (v := fun _ : ℝ => ((-8 : ℝ) : EReal)) (f := atTop))

lemma global_fifth_rate {x : X} (hx : x ∈ K) : globalMu 5 x = -8 := by
  have hfinite := global_cumulative_finite hx (k := 4) (by norm_num)
  simp only [globalMu, globalCumulative, global_cumulative_five hx]
  rw [EReal.toReal_add hfinite.1 hfinite.2 (by simp) (by simp)]
  norm_num

lemma global_w_five {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) :
    globalThesisSetting.w 5 t x = radialJacobian t (q₁ x) * radialJacobian t (q₂ x) * Real.exp (-8 * t) := by
  have he : globalThesisSetting.w 5 t x = ∏ i : Fin 5, system.σ t x i := by
    unfold ThesisSetting.w
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro i _
    exact globalThesisSetting_s x i
  rw [he, flow_singularValues_product ht hx]

lemma global_w_five_le {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ K) :
    globalThesisSetting.w 5 t x ≤ Real.exp (-4 * t) := by
  rw [global_w_five ht hx]
  have h₁ := radialJacobian_bounds ht (show q₁ x ∈ Icc (0 : ℝ) 2 from ⟨q₁_nonneg x, hx.1⟩)
  have h₂ := radialJacobian_bounds ht (show q₂ x ∈ Icc (0 : ℝ) 2 from ⟨q₂_nonneg x, hx.2.1⟩)
  calc
    _ ≤ (Real.exp (2 * t) * Real.exp (2 * t)) * Real.exp (-8 * t) := by
      gcongr
      · exact (radialJacobian_pos ht _).le
      · exact h₁.2
      · exact h₂.2
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

lemma globalCumulative_five_le {x : X} (hx : x ∈ K) : globalCumulative 5 x ≤ -4 := by
  have he : globalThesisSetting.cumulativeLocalExponent 5 x ≤ ((-4 : ℝ) : EReal) := by
    rw [global_cumulative_eq_limsup hx (by norm_num)]
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    apply EReal.coe_le_coe
    apply (div_le_iff₀ ht).mpr
    have hh := Real.log_le_log (global_w_pos ht.le hx (by norm_num)) (global_w_five_le ht.le hx)
    simpa using hh
  simpa [globalCumulative] using EReal.toReal_le_toReal he
    (global_cumulative_finite hx (by norm_num)).2 (by simp)

lemma globalCumulative_torus {x : X} (hx : x ∈ T) {k : ℕ} (hk : k ≤ 5) :
    globalCumulative k x = exponentSum torusRates k := by
  have hh := torusThesisSetting_cumulative hx hk
  change globalThesisSetting.cumulativeLocalExponent k x = _ at hh
  simp [globalCumulative, hh]

lemma global_firstIndex : globalThesisSetting.FirstDimensionIndex 4 globalMu := by
  constructor
  · intro x hx
    rw [globalMu_sum]
    exact (globalCumulative_five_le hx).trans_lt (by norm_num)
  · intro m hm hneg
    obtain ⟨x, hx⟩ := nonempty_T
    have hh := hneg x (T_subset_K hx)
    rw [globalMu_sum, globalCumulative_torus hx (by omega)] at hh
    interval_cases m <;> norm_num [exponentSum, torusRates, spectrum, Finset.sum_range_succ] at hh

lemma global_localDimension_torus {x : X} (hx : x ∈ T) :
    globalThesisSetting.localLyapunovDimension 4 globalMu x = 9 / 2 := by
  unfold ThesisSetting.localLyapunovDimension
  rw [globalMu_sum, global_fifth_rate (T_subset_K hx), globalCumulative_torus hx (by norm_num)]
  norm_num [exponentSum, torusRates, spectrum, Finset.sum_range_succ]

lemma equilibrium_global_w_exp (r s : RadialType) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ 5) :
    globalThesisSetting.w k t (pack (r.point a) (s.point b) 0) =
      Real.exp (exponentSum (radialPairSpectrum r s).rates k * t) := by
  unfold ThesisSetting.w
  calc
    _ = ∏ i ∈ Finset.range k, Real.exp ((radialPairSpectrum r s).rates i * t) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [globalThesisSetting_s _ (⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩ : Fin 5),
        equilibrium_singularValues r s ha hb ht]
    _ = _ := by rw [← Real.exp_sum, ← Finset.sum_mul]; rfl

lemma equilibrium_globalCumulative (r s : RadialType) {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {k : ℕ} (hk : k ≤ 5) :
    globalCumulative k (pack (r.point a) (s.point b) 0) = exponentSum (radialPairSpectrum r s).rates k := by
  have he : (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) * ThesisSetting.extendedLog
      (globalThesisSetting.w k t (pack (r.point a) (s.point b) 0))) =ᶠ[atTop]
      (fun _ => (exponentSum (radialPairSpectrum r s).rates k : EReal)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [equilibrium_global_w_exp r s ha hb ht.le hk, ThesisSetting.extendedLog,
      if_neg (Real.exp_pos _).ne', Real.log_exp, ← EReal.coe_mul]
    congr 1
    field_simp
  have hh := (tendsto_const_nhds.congr' he.symm).limsup_eq
  unfold globalCumulative ThesisSetting.cumulativeLocalExponent
  rw [hh]
  simp

lemma recurrent_globalCumulative_four {x : X}
    (hx : StationarySolution flow x ∨ PeriodicSolution flow x) : globalCumulative 4 x ≤ -2 := by
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
  rw [heq, equilibrium_globalCumulative r s ha hb (by norm_num)]
  rcases hrs with rfl | rfl
  · cases s <;> norm_num [radialPairSpectrum, SpectrumType.rates, exponentSum, spectrum, Finset.sum_range_succ]
  · cases r <;> norm_num [radialPairSpectrum, SpectrumType.rates, exponentSum, spectrum, Finset.sum_range_succ]

lemma recurrent_global_localDimension {x : X} (hxK : x ∈ K)
    (hx : StationarySolution flow x ∨ PeriodicSolution flow x) :
    globalThesisSetting.localLyapunovDimension 4 globalMu x ≤ 15 / 4 := by
  have hh := recurrent_globalCumulative_four hx
  unfold ThesisSetting.localLyapunovDimension
  rw [globalMu_sum, global_fifth_rate hxK]
  norm_num
  linarith

theorem global_thesis_no_attainment : ¬ globalThesisSetting.StationaryOrPeriodicSupremumAttainment 4 globalMu := by
  apply no_thesis_attainment_of_gap globalThesisSetting 4 globalMu (15 / 4)
  · obtain ⟨x, hx⟩ := nonempty_T
    refine ⟨x, T_subset_K hx, ?_⟩
    rw [global_localDimension_torus hx]
    norm_num
  · intro x hxK hx
    exact recurrent_global_localDimension hxK hx

end Eden.PolynomialCounterexample
