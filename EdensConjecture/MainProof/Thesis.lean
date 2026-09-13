import EdensConjecture.MainProof.Spectral
import EdensConjecture.MainProof.SNumbers
import EdensConjecture.MainProof.Regularity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate
namespace Eden.PolynomialCounterexample

def remainderConstant (t : ℝ) : ℝ :=
  if ht : 0 ≤ t then (flow_remainder_bound ht).choose else 0

lemma remainderConstant_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ remainderConstant t := by
  simpa [remainderConstant, ht] using (flow_remainder_bound ht).choose_spec.1

lemma remainderConstant_bound {t : ℝ} (ht : 0 ≤ t) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    ‖flow t y - flow t x - fderiv ℝ (flow t) x (y - x)‖ ≤ remainderConstant t * ‖y - x‖ ^ 2 := by
  simpa [remainderConstant, ht] using (flow_remainder_bound ht).choose_spec.2 x hx y hy

def globalThesisSetting : ThesisSetting X where
  X := K
  nonempty_X := nonempty_K
  compact_X := isCompact_K
  S := flow
  initial := flow_zero
  semigroup := fun t s ht hs x => (flow_comp ht hs x).symm
  continuous_space := fun t ht => (contDiff_flow ht).continuous
  continuous_on_X := by
    intro p hp
    exact (contDiffAt_jointFlow p (le_of_lt hp.1)).continuousAt.continuousWithinAt
  invariant_X := fun t ht => flow_image_K ht
  S' := fun t x => fderiv ℝ (flow t) x
  derivative_continuous := by
    intro p hp
    exact (continuousAt_jointDerivative p (show 0 ≤ p.1 from le_of_lt hp.1)).continuousWithinAt
  derivative_injective := fun t ht x _ => derivative_injective ht.le x
  derivative_CC := fun _ _ _ _ => finiteDimensional_CC _
  derivative_cocycle := fun t s ht hs x _ => derivative_cocycle ht.le hs.le x
  short_time_bound := derivative_short_time_bound
  P := fun t x => operatorPositivePart (fderiv ℝ (flow t) x)
  positive_part := fun _ _ _ _ => operatorPositivePart_spec _
  c := remainderConstant
  remainder := fun r => r ^ 2
  c_nonneg := fun _ ht => remainderConstant_nonneg ht.le
  remainder_nonneg := fun r _ => sq_nonneg r
  remainder_zero := by simp
  remainder_small := by
    have he : (fun r : ℝ => r ^ 2 / r) =ᶠ[𝓝[>] 0] (fun r => r) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simpa [pow_two] using (mul_div_cancel_right₀ r (ne_of_gt hr))
    exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.congr' he.symm
  frechet_type_condition := fun t ht y hy x hx => remainderConstant_bound ht.le hx hy

lemma globalThesisSetting_globalAttractor : globalThesisSetting.IsGlobalAttractor := by
  intro B hB
  exact uniformlyAttracts_K B hB

lemma globalThesisSetting_s {t : ℝ} (x : X) (j : Fin 5) :
    globalThesisSetting.s (j.val + 1) t x = system.σ t x j := by
  exact sNumber_operatorPositivePart (fderiv ℝ (flow t) x) ⟨j.val, by simpa [X, PhaseSpace] using j.isLt⟩

lemma flow_image_T {t : ℝ} (ht : 0 ≤ t) : flow t '' T = T := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨by rw [q₁_flow ht, hx.1, squaredRadius_at_one],
      by rw [q₂_flow ht, hx.2.1, squaredRadius_at_one], by simp [flow, hx.2.2]⟩
  · intro x hx
    have hxK : x ∈ flow t '' K := by rw [flow_image_K ht]; exact T_subset_K hx
    obtain ⟨y, hy, hxy⟩ := hxK
    refine ⟨y, ?_, hxy⟩
    refine ⟨?_, ?_, hy.2.2⟩
    · apply (strictMono_squaredRadius ht).injective
      rw [squaredRadius_at_one, ← q₁_flow ht, hxy, hx.1]
    · apply (strictMono_squaredRadius ht).injective
      rw [squaredRadius_at_one, ← q₂_flow ht, hxy, hx.2.1]

def torusThesisSetting : ThesisSetting X :=
  { globalThesisSetting with
    X := T
    nonempty_X := nonempty_T
    compact_X := isCompact_T
    continuous_on_X := globalThesisSetting.continuous_on_X.mono
      (fun _ hp => ⟨hp.1, T_subset_K hp.2⟩)
    invariant_X := fun _ ht => flow_image_T ht
    derivative_continuous := globalThesisSetting.derivative_continuous.mono
      (fun _ hp => ⟨hp.1, T_subset_K hp.2⟩)
    derivative_injective := fun t ht x hx => globalThesisSetting.derivative_injective t ht x (T_subset_K hx)
    derivative_CC := fun t ht x hx => globalThesisSetting.derivative_CC t ht x (T_subset_K hx)
    derivative_cocycle := fun t s ht hs x hx => globalThesisSetting.derivative_cocycle t s ht hs x (T_subset_K hx)
    short_time_bound := by
      obtain ⟨M, hM⟩ := globalThesisSetting.short_time_bound
      exact ⟨M, fun t ht ht₁ x hx => hM t ht ht₁ x (T_subset_K hx)⟩
    positive_part := fun t ht x hx => globalThesisSetting.positive_part t ht x (T_subset_K hx)
    frechet_type_condition := fun t ht y hy x hx => globalThesisSetting.frechet_type_condition t ht
      y (T_subset_K hy) x (T_subset_K hx) }

def torusRates : ℕ → ℝ := spectrum 2 2 0 0 (-8)
def torusMu (i : ℕ) (_x : X) : ℝ := torusRates (i - 1)

lemma torusThesisSetting_s_exp {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ T) (j : Fin 5) :
    torusThesisSetting.s (j.val + 1) t x = Real.exp (torusRates j * t) := by
  change globalThesisSetting.s (j.val + 1) t x = _
  rw [globalThesisSetting_s, torus_singularValues ht hx]
  fin_cases j <;> simp [torusRates, spectrum, torusSingularValues]

lemma torusThesisSetting_w_exp {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ T)
    {k : ℕ} (hk : k ≤ 5) :
    torusThesisSetting.w k t x = Real.exp (exponentSum torusRates k * t) := by
  unfold ThesisSetting.w
  calc
    (∏ i ∈ Finset.range k, torusThesisSetting.s (i + 1) t x) =
        ∏ i ∈ Finset.range k, Real.exp (torusRates i * t) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact torusThesisSetting_s_exp ht hx ⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩
    _ = _ := by rw [← Real.exp_sum, ← Finset.sum_mul]; rfl

lemma torusThesisSetting_cumulative {x : X} (hx : x ∈ T) {k : ℕ} (hk : k ≤ 5) :
    torusThesisSetting.cumulativeLocalExponent k x = (exponentSum torusRates k : EReal) := by
  have he : (fun t : ℝ => ((t⁻¹ : ℝ) : EReal) *
      ThesisSetting.extendedLog (torusThesisSetting.w k t x)) =ᶠ[atTop]
      (fun _ => (exponentSum torusRates k : EReal)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [torusThesisSetting_w_exp ht.le hx hk, ThesisSetting.extendedLog,
      if_neg (Real.exp_pos _).ne', Real.log_exp, ← EReal.coe_mul]
    congr 1
    field_simp
  exact (tendsto_const_nhds.congr' he.symm).limsup_eq

lemma torusThesisSetting_realSpectrum : torusThesisSetting.RealLocalSpectrumThrough 4 torusMu := by
  intro x hx k hk
  rw [torusThesisSetting_cumulative hx hk]
  simp [torusMu, exponentSum]

lemma torusThesisSetting_firstIndex : torusThesisSetting.FirstDimensionIndex 4 torusMu := by
  constructor
  · intro x _
    norm_num [torusMu, torusRates, spectrum, Finset.sum_range_succ]
  · intro m hm hneg
    obtain ⟨x, hx⟩ := nonempty_T
    have hh := hneg x hx
    interval_cases m <;> norm_num [torusMu, torusRates, spectrum, Finset.sum_range_succ] at hh

lemma torusThesisSetting_fifth_negative : ∀ x ∈ torusThesisSetting.X, torusMu (4 + 1) x < 0 := by
  intro x _
  norm_num [torusMu, torusRates, spectrum]

lemma torusThesisSetting_localDimension (x : X) :
    torusThesisSetting.localLyapunovDimension 4 torusMu x = 9 / 2 := by
  norm_num [ThesisSetting.localLyapunovDimension, torusMu, torusRates, spectrum, Finset.sum_range_succ]

lemma torusThesisSetting_dimensionExpression {t : ℝ} (ht : 0 ≤ t) {x : X} (hx : x ∈ T) (d : ℝ) :
    torusThesisSetting.dimensionExpression 4 d t x = Real.exp ((36 - 8 * d) * t) := by
  unfold ThesisSetting.dimensionExpression
  rw [torusThesisSetting_w_exp ht hx (by norm_num)]
  have hs := torusThesisSetting_s_exp ht hx (⟨4, by decide⟩ : Fin 5)
  rw [hs]
  norm_num [exponentSum, torusRates, spectrum, Finset.sum_range_succ]
  rw [← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

lemma torusThesisSetting_dimensionSup {t : ℝ} (ht : 0 ≤ t) (d : ℝ) :
    sSup (torusThesisSetting.dimensionExpression 4 d t '' T) = Real.exp ((36 - 8 * d) * t) := by
  have he : torusThesisSetting.dimensionExpression 4 d t '' T = {Real.exp ((36 - 8 * d) * t)} := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact torusThesisSetting_dimensionExpression ht hx d
    · intro ha
      obtain ⟨x, hx⟩ := nonempty_T
      exact ⟨x, hx, (torusThesisSetting_dimensionExpression ht hx d).trans ha.symm⟩
  rw [he, csSup_singleton]

lemma torusThesisSetting_DO_le : torusThesisSetting.douadyOesterleDimension 4 ≤ ((9 / 2 : ℝ) : EReal) := by
  have hle : ∀ d : ℝ, 9 / 2 < d → torusThesisSetting.douadyOesterleDimension 4 ≤ (d : EReal) := by
    intro d hd
    apply sInf_le
    refine ⟨d, by linarith, rfl, ?_⟩
    have ht : Tendsto (fun t : ℝ => Real.exp ((36 - 8 * d) * t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by linarith : 36 - 8 * d < 0)).mpr tendsto_id)
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (torusThesisSetting_dimensionSup ht d).symm
  have hlim : Tendsto (fun d : ℝ => (d : EReal)) (𝓝[>] (9 / 2 : ℝ)) (𝓝 ((9 / 2 : ℝ) : EReal)) :=
    tendsto_nhdsWithin_of_tendsto_nhds continuous_coe_real_ereal.continuousAt
  exact ge_of_tendsto hlim (by filter_upwards [self_mem_nhdsWithin] with d hd; exact hle d hd)

lemma torusThesisSetting_critical_exists : ∃ x : X, torusThesisSetting.CriticalPath 4 torusMu x := by
  obtain ⟨x, hx⟩ := nonempty_T
  refine ⟨x, hx, ?_⟩
  rw [torusThesisSetting_localDimension]
  exact torusThesisSetting_DO_le

lemma torusThesisSetting_no_recurrent_critical :
    ¬ ∃ x : X, torusThesisSetting.CriticalPath 4 torusMu x ∧
      (StationarySolution torusThesisSetting.S x ∨ PeriodicSolution torusThesisSetting.S x) := by
  rintro ⟨x, hx, hs | hp⟩
  · exact no_stationary_on_T hx.1 hs
  · exact no_periodic_on_T hx.1 hp

end Eden.PolynomialCounterexample
