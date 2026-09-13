import EdensConjecture.EmbeddedStrangeProof.Scalar
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

def cantorTerm (e : ℕ → Bool) (j : ℕ) : ℝ :=
  if e j then contraction ^ j else 0

theorem cantorTerm_nonneg (e : ℕ → Bool) (j : ℕ) : 0 ≤ cantorTerm e j := by
  unfold cantorTerm contraction
  split_ifs <;> positivity

theorem cantorTerm_le (e : ℕ → Bool) (j : ℕ) : cantorTerm e j ≤ contraction ^ j := by
  unfold cantorTerm
  split_ifs
  · exact le_rfl
  · exact pow_nonneg (by norm_num [contraction]) j

theorem summable_cantorTerm (e : ℕ → Bool) : Summable (cantorTerm e) := by
  apply (summable_geometric_of_lt_one
    (show 0 ≤ contraction by norm_num [contraction])
    (show contraction < 1 by norm_num [contraction])).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (cantorTerm_nonneg e j)]
  exact cantorTerm_le e j

def cantorCode (e : ℕ → Bool) : ℝ := (1 - contraction) * ∑' j, cantorTerm e j
def cantorSet : Set ℝ := range cantorCode

theorem cantorCode_mem (e : ℕ → Bool) : cantorCode e ∈ Icc (0 : ℝ) 1 := by
  have hnonneg : 0 ≤ ∑' j, cantorTerm e j := tsum_nonneg (cantorTerm_nonneg e)
  have hupper := (summable_cantorTerm e).tsum_le_tsum (cantorTerm_le e)
    (summable_geometric_of_lt_one (show 0 ≤ contraction by norm_num [contraction])
      (show contraction < 1 by norm_num [contraction]))
  rw [tsum_geometric_of_lt_one (by norm_num [contraction])
    (by norm_num [contraction])] at hupper
  norm_num [contraction] at hupper
  dsimp [cantorCode, contraction]
  constructor <;> linarith

theorem cantorSet_subset : cantorSet ⊆ Icc (0 : ℝ) 1 := by
  rintro x ⟨e, rfl⟩
  exact cantorCode_mem e

theorem zero_mem_cantorSet : (0 : ℝ) ∈ cantorSet := by
  refine ⟨fun _ => false, ?_⟩
  simp [cantorCode, cantorTerm]

theorem one_mem_cantorSet : (1 : ℝ) ∈ cantorSet := by
  refine ⟨fun _ => true, ?_⟩
  change (1 - contraction) * (∑' j : ℕ, contraction ^ j) = 1
  rw [tsum_geometric_of_lt_one (by norm_num [contraction])
    (by norm_num [contraction])]
  norm_num [contraction]

theorem continuous_cantorTerm (j : ℕ) : Continuous (fun e => cantorTerm e j) := by
  have hc : Continuous (fun b : Bool => if b then contraction ^ j else (0 : ℝ)) :=
    continuous_of_discreteTopology
  exact hc.comp (continuous_apply j)

theorem continuous_cantorCode : Continuous cantorCode := by
  apply continuous_const.mul
  apply continuous_tsum continuous_cantorTerm
    (summable_geometric_of_lt_one (show 0 ≤ contraction by norm_num [contraction])
      (show contraction < 1 by norm_num [contraction]))
  intro j e
  rw [Real.norm_eq_abs, abs_of_nonneg (cantorTerm_nonneg e j)]
  exact cantorTerm_le e j

theorem isCompact_cantorSet : IsCompact cantorSet :=
  isCompact_range continuous_cantorCode

theorem isClosed_cantorSet : IsClosed cantorSet := isCompact_cantorSet.isClosed

/-- Order-theoretic endpoints of the gap containing an interior point. -/
def lowerEndpoint (x : ℝ) : ℝ := sSup (cantorSet ∩ Iic x)
def upperEndpoint (x : ℝ) : ℝ := sInf (cantorSet ∩ Ici x)

theorem lowerEndpoint_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    lowerEndpoint x ∈ cantorSet ∩ Iic x := by
  exact (isCompact_cantorSet.inter_right isClosed_Iic).sSup_mem
    ⟨0, zero_mem_cantorSet, hx.1⟩

theorem upperEndpoint_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    upperEndpoint x ∈ cantorSet ∩ Ici x := by
  exact (isCompact_cantorSet.inter_right isClosed_Ici).sInf_mem
    ⟨1, one_mem_cantorSet, hx.2⟩

theorem endpoint_bounds {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ lowerEndpoint x ∧ lowerEndpoint x ≤ x ∧
      x ≤ upperEndpoint x ∧ upperEndpoint x ≤ 1 := by
  have hl := lowerEndpoint_mem hx
  have hu := upperEndpoint_mem hx
  exact ⟨(cantorSet_subset hl.1).1, hl.2, hu.2, (cantorSet_subset hu.1).2⟩

def gapFunction (x : ℝ) : ℝ :=
  if x ∈ Icc (0 : ℝ) 1 then (x - lowerEndpoint x) ^ 2 * (upperEndpoint x - x) ^ 2
  else 0

theorem gapFunction_nonneg (x : ℝ) : 0 ≤ gapFunction x := by
  unfold gapFunction
  split_ifs <;> positivity

theorem gapFunction_zero_on_cantor {x : ℝ} (hx : x ∈ cantorSet) : gapFunction x = 0 := by
  have hl : lowerEndpoint x = x :=
    (show IsGreatest (cantorSet ∩ Iic x) x from
      ⟨⟨hx, Set.mem_Iic.mpr le_rfl⟩, fun _ hy => Set.mem_Iic.mp hy.2⟩).csSup_eq
  simp [gapFunction, hl]

theorem gapFunction_zero_outside {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    gapFunction x = 0 := by simp [gapFunction, hx]

theorem gapFunction_le (x : ℝ) : gapFunction x ≤ 1 / 16 := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [gapFunction, if_pos hx]
    obtain ⟨hl0, hlx, hxu, hu1⟩ := endpoint_bounds hx
    have hp : 0 ≤ x - lowerEndpoint x := sub_nonneg.mpr hlx
    have hq : 0 ≤ upperEndpoint x - x := sub_nonneg.mpr hxu
    have hsum : (x - lowerEndpoint x) + (upperEndpoint x - x) ≤ 1 := by linarith
    have hsumsq := mul_self_le_mul_self (add_nonneg hp hq) hsum
    have hpq : (x - lowerEndpoint x) * (upperEndpoint x - x) ≤ 1 / 4 := by
      nlinarith [sq_nonneg ((x - lowerEndpoint x) - (upperEndpoint x - x))]
    have hs := mul_self_le_mul_self (mul_nonneg hp hq) hpq
    nlinarith
  · rw [gapFunction_zero_outside hx]
    norm_num

theorem gapFunction_pos_of_not_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hnot : x ∉ cantorSet) : 0 < gapFunction x := by
  have hl := lowerEndpoint_mem hx
  have hu := upperEndpoint_mem hx
  have hlne : lowerEndpoint x ≠ x := by
    intro h
    exact hnot (h ▸ hl.1)
  have hune : x ≠ upperEndpoint x := by
    intro h
    exact hnot (h.symm ▸ hu.1)
  have hlt : lowerEndpoint x < x := lt_of_le_of_ne hl.2 hlne
  have hut : x < upperEndpoint x := lt_of_le_of_ne hu.2 hune
  rw [gapFunction, if_pos hx]
  exact mul_pos (sq_pos_of_pos (sub_pos.mpr hlt)) (sq_pos_of_pos (sub_pos.mpr hut))

end Eden.StrangeProof.Direct
