import EdensConjecture.EmbeddedStrangeProof.C1Glue
import EdensConjecture.EmbeddedStrangeProof.ForcedODE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

def transitionPost (p : ℝ × ℝ) : ℝ :=
  p.1 * (Real.exp (2 * p.2 / p.1) - 1) / (Real.exp (2 * p.2 / p.1) + 1)

theorem transitionPost_zero (a : ℝ) : transitionPost (a, 0) = 0 := by simp [transitionPost]

theorem contDiffAt_transitionPost {p : ℝ × ℝ} (ha : p.1 ≠ 0) :
    ContDiffAt ℝ 1 transitionPost p := by
  have he : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Real.exp (2 * q.2 / q.1)) p :=
    ((contDiffAt_const.mul contDiffAt_snd).div contDiffAt_fst ha).exp
  exact (contDiffAt_fst.mul (he.sub contDiffAt_const)).div (he.add contDiffAt_const)
    (by linarith [Real.exp_pos (2 * p.2 / p.1)])

theorem hasFDerivAt_transitionPost_zero {a : ℝ} (ha : a ≠ 0) :
    HasFDerivAt transitionPost (ContinuousLinearMap.snd ℝ ℝ ℝ) (a, 0) := by
  have hfst := hasFDerivAt_fst (𝕜 := ℝ) (p := (a, (0 : ℝ)))
  have hsnd := hasFDerivAt_snd (𝕜 := ℝ) (p := (a, (0 : ℝ)))
  have he := (Eden.StrangeProof.hasFDerivAt_real_div (hsnd.const_mul 2) hfst ha).exp
  have hraw := Eden.StrangeProof.hasFDerivAt_real_div (hfst.mul (he.sub_const 1)) (he.add_const 1) (by simp)
  norm_num [Pi.mul_apply, smul_smul, ha] at hraw
  convert! hraw using 1

def middleClamp (p : ℝ × ℝ) : ℝ := if 0 ≤ p.2 then p.2 else transitionPost p

theorem contDiffOn_middleClamp :
    ContDiffOn ℝ 1 middleClamp {p : ℝ × ℝ | 0 < p.1} := by
  have h := Eden.StrangeProof.contDiffOn_ite_le_of_matching_derivatives
    (f := fun p : ℝ × ℝ => p.2) (g := transitionPost) (h := fun p => -p.2)
    (isOpen_lt continuous_const continuous_fst) continuous_snd.neg
    contDiff_snd.contDiffOn
    (fun p hp => (contDiffAt_transitionPost (ne_of_gt hp)).contDiffWithinAt)
    (by
      intro p hp hz
      have hv : p.2 = 0 := by linarith
      simp [transitionPost, hv])
    (by
      intro p hp hz
      have hv : p.2 = 0 := by linarith
      have hd : HasFDerivAt transitionPost (ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
        simpa only [← hv] using hasFDerivAt_transitionPost_zero (ne_of_gt hp)
      exact (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).fderiv.trans hd.fderiv.symm)
  convert! h using 1
  funext p
  simp only [middleClamp, neg_nonpos]

theorem transitionPost_eq_negativeFlow {a z : ℝ} (ha : a ≠ 0) :
    transitionPost (a, z) = negativeFlow a (-z / a ^ 2) 0 := by
  have he : -2 * a * (-z / a ^ 2) = 2 * z / a := by field_simp <;> ring
  simp only [transitionPost, negativeFlow, sub_zero, add_zero, he]
  have hD : a + a * Real.exp (2 * z / a) = a * (Real.exp (2 * z / a) + 1) := by ring
  rw [hD]
  field_simp
  <;> ring

theorem middleFlow_eq_middleClamp {a : ℝ} (ha : 0 < a) (t v : ℝ) :
    middleFlow a t v = middleClamp (a, v - a ^ 2 * t) := by
  have he : t ≤ v / a ^ 2 ↔ 0 ≤ v - a ^ 2 * t := by
    rw [le_div_iff₀ (sq_pos_of_pos ha)]
    constructor <;> intro h <;> nlinarith
  simp only [middleFlow, middleClamp, he]
  split_ifs with h
  · rfl
  · rw [transitionPost_eq_negativeFlow ha.ne']
    congr 1
    field_simp
    <;> ring

theorem contDiffAt_middleFlow {a v t : ℝ} (ha : 0 < a) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => middleFlow p.1 t p.2) (a, v) := by
  have hp : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => (p.1, p.2 - p.1 ^ 2 * t)) (a, v) := by fun_prop
  have hc := (contDiffOn_middleClamp.contDiffAt
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ha)).comp (a, v) hp
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (Ioi_mem_nhds ha)] with p hp
  exact middleFlow_eq_middleClamp hp t p.2

end Eden.StrangeProof.Direct
