import EdensConjecture.EmbeddedStrangeProof.Dimension

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Metric Filter MeasureTheory.Measure
open scoped NNReal ENNReal Topology MeasureTheory

def gridCount (n : ℕ) : ℕ := ⌈(contraction ^ n)⁻¹⌉₊

theorem contraction_pow_pos (n : ℕ) : 0 < contraction ^ n :=
  pow_pos (by norm_num [contraction]) n

theorem contraction_pow_le_one (n : ℕ) : contraction ^ n ≤ 1 :=
  pow_le_one₀ (by norm_num [contraction]) (by norm_num [contraction])

theorem gridCount_pos (n : ℕ) : 0 < gridCount n := by
  apply Nat.one_le_ceil_iff.mpr
  exact inv_pos.mpr (contraction_pow_pos n)

theorem gridLength_le (n : ℕ) : (gridCount n : ℝ)⁻¹ ≤ contraction ^ n := by
  have hN : 0 < (gridCount n : ℝ) := by exact_mod_cast gridCount_pos n
  have h := mul_le_mul_of_nonneg_left (Nat.le_ceil ((contraction ^ n)⁻¹))
    (contraction_pow_pos n).le
  rw [mul_inv_cancel₀ (contraction_pow_pos n).ne'] at h
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hN).mpr
  simpa [gridCount, mul_comm] using h

theorem gridCount_scaled_le (n : ℕ) : ((gridCount n : ℝ) + 1) * contraction ^ n ≤ 3 := by
  have h := mul_le_mul_of_nonneg_right
    (Nat.ceil_lt_add_one (inv_nonneg.mpr (contraction_pow_pos n).le)).le
    (contraction_pow_pos n).le
  change (gridCount n : ℝ) * contraction ^ n ≤ ((contraction ^ n)⁻¹ + 1) * contraction ^ n at h
  rw [add_mul, inv_mul_cancel₀ (contraction_pow_pos n).ne', one_mul] at h
  nlinarith [contraction_pow_le_one n]

def gridInterval (n : ℕ) (i : Fin (gridCount n + 1)) : Set ℝ :=
  Icc ((i : ℝ) / gridCount n) (((i : ℝ) + 1) / gridCount n)

theorem gridInterval_ediam (n : ℕ) (i : Fin (gridCount n + 1)) :
    ediam (gridInterval n i) = ENNReal.ofReal ((gridCount n : ℝ)⁻¹) := by
  rw [gridInterval, Real.ediam_Icc]
  congr 1
  ring

theorem unitInterval_subset_grid (n : ℕ) : Icc (0 : ℝ) 1 ⊆ ⋃ i, gridInterval n i := by
  intro y hy
  have hN : 0 < (gridCount n : ℝ) := by exact_mod_cast gridCount_pos n
  have hf := Nat.floor_le (mul_nonneg hN.le hy.1)
  have hh := Nat.lt_floor_add_one ((gridCount n : ℝ) * y)
  have hi : ⌊(gridCount n : ℝ) * y⌋₊ ≤ gridCount n := by
    have hbound : (⌊(gridCount n : ℝ) * y⌋₊ : ℝ) ≤ (gridCount n : ℝ) :=
      hf.trans (by nlinarith [hy.2])
    exact_mod_cast hbound
  refine mem_iUnion.mpr ⟨⟨⌊(gridCount n : ℝ) * y⌋₊, Nat.lt_succ_of_le hi⟩, ?_⟩
  constructor
  · exact (div_le_iff₀ hN).mpr (by simpa [mul_comm] using hf)
  · exact (le_div_iff₀ hN).mpr (by simpa [mul_comm] using hh.le)

def teethCube : Set (Fin 4 → ℝ) :=
  Set.pi univ (Fin.cons cantorSet (fun _ : Fin 3 => Icc (0 : ℝ) 1))

abbrev ProductCoverIndex (n : ℕ) := (Fin n → Bool) × (Fin 3 → Fin (gridCount n + 1))

def productCoverBox (n : ℕ) (i : ProductCoverIndex n) : Set (Fin 4 → ℝ) :=
  Set.pi univ (Fin.cons (cantorCoverInterval n i.1) (fun j => gridInterval n (i.2 j)))

theorem productCoverBox_ediam_le (n : ℕ) (i : ProductCoverIndex n) :
    ediam (productCoverBox n i) ≤ ENNReal.ofReal (contraction ^ n) := by
  apply ediam_pi_le_of_le
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · exact (cantorCoverInterval_ediam n i.1).le
  · exact (gridInterval_ediam n (i.2 k)).le.trans (ENNReal.ofReal_le_ofReal (gridLength_le n))

theorem teethCube_subset_productCover (n : ℕ) : teethCube ⊆ ⋃ i, productCoverBox n i := by
  classical
  intro p hp
  obtain ⟨w, hw⟩ := mem_iUnion.mp (cantorSet_subset_prefix_cover n (hp 0 (mem_univ _)))
  have hgrid : ∀ j : Fin 3, ∃ i, p j.succ ∈ gridInterval n i := by
    intro j
    exact mem_iUnion.mp (unitInterval_subset_grid n (hp j.succ (mem_univ _)))
  choose f hf using hgrid
  refine mem_iUnion.mpr ⟨(w, f), ?_⟩
  intro j hj
  exact Fin.cases hw hf j

theorem productCover_real_cost_bound (n : ℕ) :
    (2 : ℝ) ^ n * ((gridCount n : ℝ) + 1) ^ 3 * (contraction ^ n) ^ (23 / 6 : ℝ) ≤
      27 * (2 * contraction ^ (5 / 6 : ℝ)) ^ n := by
  have hr := contraction_pow_pos n
  have hc : 0 ≤ contraction := by norm_num [contraction]
  have hexp : (contraction ^ n) ^ (23 / 6 : ℝ) =
      (contraction ^ n) ^ (3 : ℕ) * (contraction ^ n) ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_natCast (contraction ^ n) 3, ← Real.rpow_add hr]
    norm_num
  have hswap : (contraction ^ n) ^ (5 / 6 : ℝ) = (contraction ^ (5 / 6 : ℝ)) ^ n := by
    rw [← Real.rpow_natCast_mul hc, ← Real.rpow_mul_natCast hc, mul_comm]
  rw [hexp, hswap]
  calc
    _ = (((gridCount n : ℝ) + 1) * contraction ^ n) ^ 3 *
        (2 * contraction ^ (5 / 6 : ℝ)) ^ n := by rw [mul_pow, mul_pow]; ring
    _ ≤ (3 : ℝ) ^ 3 * (2 * contraction ^ (5 / 6 : ℝ)) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (gridCount_scaled_le n) 3
    _ = _ := by norm_num

theorem productCover_sum_bound (n : ℕ) :
    (∑ i : ProductCoverIndex n, ediam (productCoverBox n i) ^ (23 / 6 : ℝ)) ≤
      ENNReal.ofReal (27 * (2 * contraction ^ (5 / 6 : ℝ)) ^ n) := by
  calc
    _ ≤ ∑ _i : ProductCoverIndex n, ENNReal.ofReal (contraction ^ n) ^ (23 / 6 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact ENNReal.rpow_le_rpow (productCoverBox_ediam_le n i) (by norm_num)
    _ = ENNReal.ofReal ((2 : ℝ) ^ n * ((gridCount n : ℝ) + 1) ^ 3 * (contraction ^ n) ^ (23 / 6 : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_rpow_of_nonneg (contraction_pow_pos n).le (by norm_num)]
      simp only [ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 by norm_num),
        ENNReal.ofReal_pow (show (0 : ℝ) ≤ (gridCount n : ℝ) + 1 by positivity),
        ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (productCover_real_cost_bound n)

theorem teethCube_hausdorffMeasure_zero : μH[23 / 6] teethCube = 0 := by
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (contraction ^ n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [contraction]) (by norm_num [contraction]))
  have hc : Tendsto (fun n : ℕ => ENNReal.ofReal (27 * (2 * contraction ^ (5 / 6 : ℝ)) ^ n))
      atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num [contraction]) _)) cantor_cover_ratio_lt_one).const_mul 27
    simpa only [mul_zero, Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp h
  have hsum : Tendsto (fun n : ℕ => ∑ i : ProductCoverIndex n,
      ediam (productCoverBox n i) ^ (23 / 6 : ℝ)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun _ => bot_le) productCover_sum_bound
  have h := hausdorffMeasure_le_liminf_sum (23 / 6) teethCube _ hr productCoverBox
    (Eventually.of_forall productCoverBox_ediam_le) (Eventually.of_forall teethCube_subset_productCover)
  rw [hsum.liminf_eq] at h
  exact le_antisymm h bot_le

theorem teethCube_dimH_upper : dimH teethCube ≤ (23 : ENNReal) / 6 := by
  have h := dimH_le_of_hausdorffMeasure_ne_top (d := (23 / 6 : ℝ≥0)) (s := teethCube) (by
    norm_num only [NNReal.coe_div, NNReal.coe_ofNat]
    rw [teethCube_hausdorffMeasure_zero]
    exact ENNReal.zero_ne_top)
  simpa using h

end Eden.StrangeProof.Direct
