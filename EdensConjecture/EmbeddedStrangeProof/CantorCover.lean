import EdensConjecture.EmbeddedStrangeProof.Cantor

noncomputable section
namespace Eden.StrangeProof.Direct
open Set
open scoped BigOperators

def cantorPrefix (e : ℕ → Bool) (n : ℕ) : ℝ :=
  (1 - contraction) * ∑ j ∈ Finset.range n, cantorTerm e j

theorem cantorCode_split (e : ℕ → Bool) (n : ℕ) :
    cantorCode e = cantorPrefix e n + contraction ^ n * cantorCode (fun j => e (j + n)) := by
  have h := (summable_cantorTerm e).sum_add_tsum_nat_add n
  have heq : (fun j => cantorTerm e (j + n)) =
      fun j => contraction ^ n * cantorTerm (fun k => e (k + n)) j := by
    funext j
    simp only [cantorTerm, pow_add]
    split_ifs <;> ring
  rw [heq, tsum_mul_left] at h
  unfold cantorCode cantorPrefix
  rw [← h]
  ring

theorem cantorCode_mem_prefix_interval (e : ℕ → Bool) (n : ℕ) :
    cantorCode e ∈ Icc (cantorPrefix e n) (cantorPrefix e n + contraction ^ n) := by
  rw [cantorCode_split e n]
  have hc := cantorCode_mem (fun j => e (j + n))
  have hr : 0 ≤ contraction ^ n := pow_nonneg (by norm_num [contraction]) n
  constructor
  · linarith [mul_nonneg hr hc.1]
  · linarith [mul_le_mul_of_nonneg_left hc.2 hr]

theorem cantorPrefix_eq_of_agree {e f : ℕ → Bool} {n : ℕ}
    (h : ∀ j < n, e j = f j) : cantorPrefix e n = cantorPrefix f n := by
  unfold cantorPrefix
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [cantorTerm, h j (Finset.mem_range.mp hj)]

theorem cantorPrefix_succ (e : ℕ → Bool) (n : ℕ) :
    cantorPrefix e (n + 1) = cantorPrefix e n + (1 - contraction) * cantorTerm e n := by
  simp only [cantorPrefix, Finset.sum_range_succ, mul_add]

theorem cantorCode_separation {e f : ℕ → Bool} {n : ℕ}
    (hbefore : ∀ j < n, e j = f j) (he : e n = false) (hf : f n = true) :
    (1 / 7 : ℝ) * contraction ^ n ≤ cantorCode f - cantorCode e := by
  have hp := cantorPrefix_eq_of_agree hbefore
  have heI := (cantorCode_mem_prefix_interval e (n + 1)).2
  have hfI := (cantorCode_mem_prefix_interval f (n + 1)).1
  rw [cantorPrefix_succ, hp] at heI
  rw [cantorPrefix_succ] at hfI
  simp only [cantorTerm, he, hf, Bool.false_eq_true, if_false, if_true, mul_zero,
    add_zero, pow_succ] at heI hfI
  dsimp [contraction] at *
  linarith

theorem cantorCode_injective : Function.Injective cantorCode := by
  intro e f hcode
  by_contra hne
  have hex : ∃ n, e n ≠ f n := by
    by_contra! h
    exact hne (funext h)
  let n := Nat.find hex
  have hn : e n ≠ f n := Nat.find_spec hex
  have hb : ∀ j < n, e j = f j := by
    intro j hj
    exact not_not.mp (Nat.find_min hex hj)
  have hr : 0 < (1 / 7 : ℝ) * contraction ^ n := by
    apply mul_pos (by norm_num)
    exact pow_pos (by norm_num [contraction]) n
  cases he : e n <;> cases hf : f n
  · exact hn (he.trans hf.symm)
  · have hs := cantorCode_separation hb he hf
    rw [hcode, sub_self] at hs
    exact (not_le.mpr hr) hs
  · have hs := cantorCode_separation (fun j hj => (hb j hj).symm) hf he
    rw [hcode, sub_self] at hs
    exact (not_le.mpr hr) hs
  · exact hn (he.trans hf.symm)

/-- The level-n construction is covered by 2^n intervals of length r^n. -/
theorem cantorSet_subset_prefix_cover (n : ℕ) :
    cantorSet ⊆ ⋃ w : Fin n → Bool,
      Icc (cantorPrefix (fun j => if h : j < n then w ⟨j, h⟩ else false) n)
        (cantorPrefix (fun j => if h : j < n then w ⟨j, h⟩ else false) n + contraction ^ n) := by
  rintro x ⟨e, rfl⟩
  apply mem_iUnion.mpr
  refine ⟨fun j => e j, ?_⟩
  have hp : cantorPrefix (fun j => if _ : j < n then e j else false) n =
      cantorPrefix e n := by
    apply cantorPrefix_eq_of_agree
    intro j hj
    simp [hj]
  rw [hp]
  exact cantorCode_mem_prefix_interval e n

end Eden.StrangeProof.Direct
