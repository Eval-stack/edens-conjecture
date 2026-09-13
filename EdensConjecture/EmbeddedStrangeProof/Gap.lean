import EdensConjecture.EmbeddedStrangeProof.Cantor
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

theorem cantor_le_lowerEndpoint {x c : ℝ} (hc : c ∈ cantorSet) (hcx : c ≤ x) :
    c ≤ lowerEndpoint x := by
  apply le_csSup
  · exact ⟨x, fun _ hy => hy.2⟩
  · exact ⟨hc, hcx⟩

theorem upperEndpoint_le_cantor {x c : ℝ} (hc : c ∈ cantorSet) (hxc : x ≤ c) :
    upperEndpoint x ≤ c := by
  apply csInf_le
  · exact ⟨x, fun _ hy => hy.2⟩
  · exact ⟨hc, hxc⟩

/-- The gap between the two selected endpoints contains no Cantor point. -/
theorem no_cantor_between_endpoints {x c : ℝ} (hc : c ∈ cantorSet)
    (hl : lowerEndpoint x < c) (hu : c < upperEndpoint x) : False := by
  rcases le_total c x with hcx | hxc
  · exact (not_lt_of_ge (cantor_le_lowerEndpoint hc hcx)) hl
  · exact (not_lt_of_ge (upperEndpoint_le_cantor hc hxc)) hu

theorem endpoints_constant_on_gap {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Ioo (lowerEndpoint x) (upperEndpoint x)) :
    lowerEndpoint y = lowerEndpoint x ∧ upperEndpoint y = upperEndpoint x := by
  have hl := lowerEndpoint_mem hx
  have hu := upperEndpoint_mem hx
  constructor
  · apply IsGreatest.csSup_eq
    refine ⟨⟨hl.1, hy.1.le⟩, ?_⟩
    intro c hc
    by_contra h
    exact no_cantor_between_endpoints hc.1 (lt_of_not_ge h) (hc.2.trans_lt hy.2)
  · apply IsLeast.csInf_eq
    refine ⟨⟨hu.1, hy.2.le⟩, ?_⟩
    intro c hc
    by_contra h
    exact no_cantor_between_endpoints hc.1 (hy.1.trans_le hc.2) (lt_of_not_ge h)

theorem gapFunction_eq_polynomial_on_gap {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Ioo (lowerEndpoint x) (upperEndpoint x)) :
    gapFunction y = (y - lowerEndpoint x) ^ 2 * (upperEndpoint x - y) ^ 2 := by
  obtain ⟨hl0, _, _, hu1⟩ := endpoint_bounds hx
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hl0.trans hy.1.le, hy.2.le.trans hu1⟩
  obtain ⟨hl, hu⟩ := endpoints_constant_on_gap hx hy
  simp [gapFunction, hy01, hl, hu]

/-- Quadratic vanishing at every Cantor point, including both endpoints. -/
theorem gapFunction_le_sq_dist {c : ℝ} (hc : c ∈ cantorSet) (y : ℝ) :
    gapFunction y ≤ (y - c) ^ 2 := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · obtain ⟨hl0, hly, hyu, hu1⟩ := endpoint_bounds hy
    have hp : 0 ≤ y - lowerEndpoint y := sub_nonneg.mpr hly
    have hq : 0 ≤ upperEndpoint y - y := sub_nonneg.mpr hyu
    have hp1 : y - lowerEndpoint y ≤ 1 := by linarith [hy.2]
    have hq1 : upperEndpoint y - y ≤ 1 := by linarith [hy.1]
    have hp2 := mul_self_le_mul_self hp hp1
    have hq2 := mul_self_le_mul_self hq hq1
    rw [gapFunction, if_pos hy]
    rcases le_total c y with hcy | hyc
    · have hcl := cantor_le_lowerEndpoint hc hcy
      have hpdist : (y - lowerEndpoint y) ^ 2 ≤ (y - c) ^ 2 := by
        exact pow_le_pow_left₀ hp (by linarith) 2
      calc
        (y - lowerEndpoint y) ^ 2 * (upperEndpoint y - y) ^ 2 ≤
            (y - lowerEndpoint y) ^ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          nlinarith
        _ ≤ (y - c) ^ 2 := by simpa using hpdist
    · have huc := upperEndpoint_le_cantor hc hyc
      have hqdist : (upperEndpoint y - y) ^ 2 ≤ (c - y) ^ 2 := by
        exact pow_le_pow_left₀ hq (by linarith) 2
      calc
        (y - lowerEndpoint y) ^ 2 * (upperEndpoint y - y) ^ 2 ≤
            1 * (upperEndpoint y - y) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          nlinarith
        _ ≤ (y - c) ^ 2 := by nlinarith
  · rw [gapFunction_zero_outside hy]
    exact sq_nonneg _

theorem continuousAt_gapFunction_on_cantor {c : ℝ} (hc : c ∈ cantorSet) :
    ContinuousAt gapFunction c := by
  rw [ContinuousAt, gapFunction_zero_on_cantor hc]
  have hlim : Tendsto (fun y : ℝ => (y - c) ^ 2) (𝓝 c) (𝓝 0) := by
    have hcont : Continuous (fun y : ℝ => (y - c) ^ 2) := by fun_prop
    simpa using hcont.tendsto c
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    gapFunction_nonneg (gapFunction_le_sq_dist hc)

theorem hasDerivAt_gapFunction_on_cantor {c : ℝ} (hc : c ∈ cantorSet) :
    HasDerivAt gapFunction 0 c := by
  have hbig : gapFunction =O[𝓝 c] (fun y : ℝ => ‖y - c‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound'
    apply Filter.Eventually.of_forall
    intro y
    simpa [Real.norm_eq_abs, abs_of_nonneg (gapFunction_nonneg y), sq_abs]
      using gapFunction_le_sq_dist hc y
  have hsmall := hbig.trans_isLittleO
    (Asymptotics.isLittleO_pow_sub_sub c (by decide : 1 < 2))
  rw [hasDerivAt_iff_isLittleO]
  simpa [gapFunction_zero_on_cantor hc] using hsmall

def gapDerivative (x : ℝ) : ℝ :=
  if x ∈ Icc (0 : ℝ) 1 then
    2 * (x - lowerEndpoint x) * (upperEndpoint x - x) *
      (lowerEndpoint x + upperEndpoint x - 2 * x)
  else 0

theorem gapDerivative_zero_on_cantor {c : ℝ} (hc : c ∈ cantorSet) :
    gapDerivative c = 0 := by
  have hl : lowerEndpoint c = c :=
    (show IsGreatest (cantorSet ∩ Iic c) c from
      ⟨⟨hc, Set.mem_Iic.mpr le_rfl⟩, fun _ hy => Set.mem_Iic.mp hy.2⟩).csSup_eq
  simp [gapDerivative, hl]

theorem eventually_gap_polynomial {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hnot : x ∉ cantorSet) :
    gapFunction =ᶠ[𝓝 x] (fun y => (y - lowerEndpoint x) ^ 2 * (upperEndpoint x - y) ^ 2) := by
  have hl := lowerEndpoint_mem hx
  have hu := upperEndpoint_mem hx
  have hlt : lowerEndpoint x < x := lt_of_le_of_ne hl.2 (by
    intro h
    exact hnot (h ▸ hl.1))
  have hut : x < upperEndpoint x := lt_of_le_of_ne hu.2 (by
    intro h
    exact hnot (h.symm ▸ hu.1))
  filter_upwards [Ioo_mem_nhds hlt hut] with y hy
  exact gapFunction_eq_polynomial_on_gap hx hy

theorem hasDerivAt_gapFunction (x : ℝ) : HasDerivAt gapFunction (gapDerivative x) x := by
  by_cases hc : x ∈ cantorSet
  · rw [gapDerivative_zero_on_cantor hc]
    exact hasDerivAt_gapFunction_on_cantor hc
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have hp := (((hasDerivAt_id x).sub_const (lowerEndpoint x)).pow 2).mul
      (((hasDerivAt_const x (upperEndpoint x)).sub (hasDerivAt_id x)).pow 2)
    have hg := hp.congr_of_eventuallyEq (eventually_gap_polynomial hx hc)
    have hd : (2 * (x - lowerEndpoint x) * (upperEndpoint x - x) ^ 2 +
        (x - lowerEndpoint x) ^ 2 * (2 * (upperEndpoint x - x) * (-1))) =
        gapDerivative x := by simp only [gapDerivative, if_pos hx]; ring
    simpa only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq, Nat.cast_ofNat,
      show 2 - 1 = (1 : ℕ) from rfl, pow_one, mul_one, sub_self, zero_sub,
      hd] using hg
  · have heq : gapFunction =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
      exact gapFunction_zero_outside hy
    simpa [gapDerivative, hx] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq

theorem continuous_gapFunction : Continuous gapFunction :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_gapFunction x).continuousAt)

theorem abs_gapDerivative_le_dist {c : ℝ} (hc : c ∈ cantorSet) (y : ℝ) :
    |gapDerivative y| ≤ 2 * |y - c| := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · obtain ⟨hl0, hly, hyu, hu1⟩ := endpoint_bounds hy
    have hp : 0 ≤ y - lowerEndpoint y := sub_nonneg.mpr hly
    have hq : 0 ≤ upperEndpoint y - y := sub_nonneg.mpr hyu
    have hp1 : y - lowerEndpoint y ≤ 1 := by linarith [hy.2]
    have hq1 : upperEndpoint y - y ≤ 1 := by linarith [hy.1]
    have habs : |lowerEndpoint y + upperEndpoint y - 2 * y| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith
    rw [gapDerivative, if_pos hy, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hp, abs_of_nonneg hq]
    have hm := mul_le_mul_of_nonneg_left habs
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp) hq)
    rcases le_total c y with hcy | hyc
    · have hcl := cantor_le_lowerEndpoint hc hcy
      have hprod := mul_le_mul_of_nonneg_left hq1
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp)
      rw [abs_of_nonneg (sub_nonneg.mpr hcy)]
      nlinarith
    · have huc := upperEndpoint_le_cantor hc hyc
      have hprod := mul_le_mul_of_nonneg_right hp1
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hq)
      rw [abs_of_nonpos (sub_nonpos.mpr hyc)]
      nlinarith
  · simp only [gapDerivative, if_neg hy, abs_zero]
    positivity

theorem continuousAt_gapDerivative_on_cantor {c : ℝ} (hc : c ∈ cantorSet) :
    ContinuousAt gapDerivative c := by
  rw [ContinuousAt, gapDerivative_zero_on_cantor hc]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim : Tendsto (fun y : ℝ => 2 * |y - c|) (𝓝 c) (𝓝 0) := by
    have hcont : Continuous (fun y : ℝ => 2 * |y - c|) := by fun_prop
    simpa using hcont.tendsto c
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => norm_nonneg _) (fun y => by
      simpa only [Real.norm_eq_abs] using abs_gapDerivative_le_dist hc y)

theorem continuous_gapDerivative : Continuous gapDerivative := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hc : x ∈ cantorSet
  · exact continuousAt_gapDerivative_on_cantor hc
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have hl := lowerEndpoint_mem hx
    have hu := upperEndpoint_mem hx
    have hlt : lowerEndpoint x < x := lt_of_le_of_ne hl.2 (by
      intro h
      exact hc (h ▸ hl.1))
    have hut : x < upperEndpoint x := lt_of_le_of_ne hu.2 (by
      intro h
      exact hc (h.symm ▸ hu.1))
    have heq : gapDerivative =ᶠ[𝓝 x] (fun y =>
        2 * (y - lowerEndpoint x) * (upperEndpoint x - y) *
          (lowerEndpoint x + upperEndpoint x - 2 * y)) := by
      filter_upwards [Ioo_mem_nhds hlt hut] with y hy
      obtain ⟨hl0, _, _, hu1⟩ := endpoint_bounds hx
      have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hl0.trans hy.1.le, hy.2.le.trans hu1⟩
      obtain ⟨hl', hu'⟩ := endpoints_constant_on_gap hx hy
      simp [gapDerivative, hy01, hl', hu']
    have hp : ContinuousAt (fun y : ℝ =>
        2 * (y - lowerEndpoint x) * (upperEndpoint x - y) *
          (lowerEndpoint x + upperEndpoint x - 2 * y)) x := by fun_prop
    exact hp.congr_of_eventuallyEq heq
  · apply (show ContinuousAt (fun _ : ℝ => (0 : ℝ)) x from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact if_neg hy

theorem contDiff_gapFunction : ContDiff ℝ 1 gapFunction := by
  apply contDiff_one_iff_deriv.mpr
  constructor
  · exact fun x => (hasDerivAt_gapFunction x).differentiableAt
  · have heq : deriv gapFunction = gapDerivative :=
      funext (fun x => (hasDerivAt_gapFunction x).deriv)
    rw [heq]
    exact continuous_gapDerivative

end Eden.StrangeProof.Direct
