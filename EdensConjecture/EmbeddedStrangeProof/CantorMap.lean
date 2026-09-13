import EdensConjecture.EmbeddedStrangeProof.CantorCover
import Mathlib.Analysis.Real.OfDigits
import Mathlib.Topology.MetricSpace.Holder

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

def binaryDigit (b : Bool) : Fin 2 := if b then 1 else 0
def binaryCode (e : ℕ → Bool) : ℝ := Real.ofDigits (fun n => binaryDigit (e n))

theorem binaryCode_mem (e : ℕ → Bool) : binaryCode e ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩

theorem binaryCode_surjOn : SurjOn binaryCode univ (Icc (0 : ℝ) 1) := by
  intro x hx
  obtain ⟨d, _, hd⟩ := Real.ofDigits_SurjOn (by decide : 1 < 2) hx
  refine ⟨fun n => decide (d n = 1), mem_univ _, ?_⟩
  have heq : (fun n => binaryDigit (decide (d n = 1))) = d := by
    funext n
    generalize d n = k
    fin_cases k <;> simp [binaryDigit]
  simpa only [binaryCode, heq] using hd

def cantorBinaryMap (x : ℝ) : ℝ := by
  classical
  exact if hx : x ∈ cantorSet then binaryCode hx.choose else 0

theorem cantorBinaryMap_code (e : ℕ → Bool) :
    cantorBinaryMap (cantorCode e) = binaryCode e := by
  classical
  have hx : cantorCode e ∈ cantorSet := mem_range_self e
  simp only [cantorBinaryMap, dif_pos hx]
  exact congrArg binaryCode (cantorCode_injective hx.choose_spec)

theorem cantorBinaryMap_image : cantorBinaryMap '' cantorSet = Icc (0 : ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    rw [cantorBinaryMap_code]
    exact binaryCode_mem e
  · intro x hx
    obtain ⟨e, _, he⟩ := binaryCode_surjOn hx
    exact ⟨cantorCode e, mem_range_self e, (cantorBinaryMap_code e).trans he⟩

theorem binaryCode_dist_le_of_agree {e f : ℕ → Bool} {n : ℕ}
    (h : ∀ j < n, e j = f j) : |binaryCode e - binaryCode f| ≤ (2 : ℝ)⁻¹ ^ n := by
  simpa only [binaryCode, Nat.cast_ofNat, inv_pow] using
    (Real.abs_ofDigits_sub_ofDigits_le (x := fun j => binaryDigit (e j))
      (y := fun j => binaryDigit (f j)) (n := n) (fun j hj => congrArg binaryDigit (h j hj)))

theorem cantorCode_abs_separation {e f : ℕ → Bool} {n : ℕ}
    (hbefore : ∀ j < n, e j = f j) (hne : e n ≠ f n) :
    (1 / 7 : ℝ) * contraction ^ n ≤ |cantorCode e - cantorCode f| := by
  cases he : e n <;> cases hf : f n
  · exact False.elim (hne (he.trans hf.symm))
  · have h := cantorCode_separation hbefore he hf
    calc
      _ ≤ cantorCode f - cantorCode e := h
      _ ≤ |cantorCode f - cantorCode e| := le_abs_self _
      _ = _ := abs_sub_comm _ _
  · exact (cantorCode_separation (fun j hj => (hbefore j hj).symm) hf he).trans (le_abs_self _)
  · exact False.elim (hne (he.trans hf.symm))

theorem binaryCode_pow_five_le (e f : ℕ → Bool) :
    |binaryCode e - binaryCode f| ^ 5 ≤ 7 ^ 4 * |cantorCode e - cantorCode f| ^ 4 := by
  by_cases heq : e = f
  · subst f
    simp
  have hex : ∃ n, e n ≠ f n := by
    by_contra! h
    exact heq (funext h)
  let n := Nat.find hex
  have hn : e n ≠ f n := Nat.find_spec hex
  have hb : ∀ j < n, e j = f j := fun j hj => not_not.mp (Nat.find_min hex hj)
  have hbin := binaryCode_dist_le_of_agree hb
  have hcan := cantorCode_abs_separation hb hn
  have hr : contraction ^ n ≤ 7 * |cantorCode e - cantorCode f| := by linarith
  calc
    _ ≤ ((2 : ℝ)⁻¹ ^ n) ^ 5 := by gcongr
    _ = ((2 : ℝ)⁻¹ ^ 5) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 5]
    _ ≤ (contraction ^ 4) ^ n := by
      gcongr
      norm_num [contraction]
    _ = (contraction ^ n) ^ 4 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 4 n]
    _ ≤ (7 * |cantorCode e - cantorCode f|) ^ 4 := by
      exact pow_le_pow_left₀ (pow_nonneg (by norm_num [contraction]) n) hr 4
    _ = _ := by ring

theorem binaryCode_holder_bound (e f : ℕ → Bool) :
    |binaryCode e - binaryCode f| ≤ 7 * |cantorCode e - cantorCode f| ^ (4 / 5 : ℝ) := by
  have hd : 0 ≤ |cantorCode e - cantorCode f| := abs_nonneg _
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by decide : 5 ≠ 0)).mp
  have hpow : (|cantorCode e - cantorCode f| ^ (4 / 5 : ℝ)) ^ (5 : ℕ) =
      |cantorCode e - cantorCode f| ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
    norm_num
  rw [mul_pow, hpow]
  exact (binaryCode_pow_five_le e f).trans (by gcongr <;> norm_num)

theorem cantorBinaryMap_holder_bound {x y : ℝ} (hx : x ∈ cantorSet) (hy : y ∈ cantorSet) :
    |cantorBinaryMap x - cantorBinaryMap y| ≤ 7 * |x - y| ^ (4 / 5 : ℝ) := by
  rcases hx with ⟨e, rfl⟩
  rcases hy with ⟨f, rfl⟩
  simpa only [cantorBinaryMap_code] using binaryCode_holder_bound e f

theorem holderOnWith_cantorBinaryMap : HolderOnWith 7 (4 / 5) cantorBinaryMap cantorSet := by
  intro x hx y hy
  have h := ENNReal.ofReal_le_ofReal (cantorBinaryMap_holder_bound hx hy)
  simpa only [edist_dist, Real.dist_eq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7),
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 / 5),
    ENNReal.ofReal_ofNat, ENNReal.coe_ofNat, NNReal.coe_div, NNReal.coe_ofNat] using h

end Eden.StrangeProof.Direct
