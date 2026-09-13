import EdensConjecture.EmbeddedStrangeProof.C1Glue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

def scaledMap (ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := p.1 * ψ (p.2 / p.1)
def scaledClamp (ψ : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ p.2 then scaledMap ψ p else p.2

theorem hasFDerivAt_scaledMap_zero {ψ : ℝ → ℝ} (hzero : ψ 0 = 0)
    (hψ : HasDerivAt ψ 1 0) {a : ℝ} (ha : a ≠ 0) :
    HasFDerivAt (scaledMap ψ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (a, 0) := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (a, (0 : ℝ)))
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (p := (a, (0 : ℝ)))
  have hdiv := Eden.StrangeProof.hasFDerivAt_real_div hs hf ha
  have hψ' : HasDerivAt ψ 1 ((a, (0 : ℝ)).2 / (a, (0 : ℝ)).1) := by simpa using hψ
  have hraw := hf.mul (hψ'.comp_hasFDerivAt (a, (0 : ℝ)) hdiv)
  simp [Function.comp_def, hzero, smul_smul, ha] at hraw
  convert! hraw using 1

theorem contDiffAt_scaledMap {ψ : ℝ → ℝ} {p : ℝ × ℝ}
    (ha : p.1 ≠ 0) (hψ : ContDiffAt ℝ 1 ψ (p.2 / p.1)) :
    ContDiffAt ℝ 1 (scaledMap ψ) p :=
  contDiffAt_fst.mul (hψ.comp p (contDiffAt_snd.div contDiffAt_fst ha))

theorem contDiffOn_scaledClamp {ψ : ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (ha : ∀ p ∈ U, p.1 ≠ 0)
    (hc : ContDiffOn ℝ 1 (scaledMap ψ) U)
    (hz : ψ 0 = 0) (hd : HasDerivAt ψ 1 0) :
    ContDiffOn ℝ 1 (scaledClamp ψ) U := by
  have h := Eden.StrangeProof.contDiffOn_ite_le_of_matching_derivatives
    (f := scaledMap ψ) (g := fun p : ℝ × ℝ => p.2) (h := fun p => -p.2)
    hU continuous_snd.neg hc contDiff_snd.contDiffOn
    (by
      intro p hp he
      have hv : p.2 = 0 := by linarith
      simp [scaledMap, hv, hz])
    (by
      intro p hp he
      have hv : p.2 = 0 := by linarith
      have hh : HasFDerivAt (scaledMap ψ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
        simpa only [← hv] using hasFDerivAt_scaledMap_zero hz hd (ha p hp)
      exact hh.fderiv.trans (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).fderiv.symm)
  convert! h using 1
  funext p
  simp only [scaledClamp, neg_nonpos]

theorem contDiffOn_atanClamp :
    ContDiffOn ℝ 1 (scaledClamp Real.arctan) {p : ℝ × ℝ | 0 < p.1} := by
  apply contDiffOn_scaledClamp (isOpen_lt continuous_const continuous_fst)
    (fun p hp => ne_of_gt hp)
    (fun p hp => (contDiffAt_scaledMap (ne_of_gt hp) Real.contDiff_arctan.contDiffAt).contDiffWithinAt)
    Real.arctan_zero
  simpa using Real.hasDerivAt_arctan 0

theorem contDiffAt_tanClamp {p : ℝ × ℝ} (ha : 0 < p.1)
    (hθ : p.2 < (Real.pi / 2) * p.1) :
    ContDiffAt ℝ 1 (scaledClamp Real.tan) p := by
  by_cases hz : p.2 < 0
  · apply contDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.eventually (Iio_mem_nhds hz)] with q hq
    exact if_neg (not_le.mpr hq)
  let U : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ -(Real.pi / 2) * q.1 < q.2 ∧ q.2 < (Real.pi / 2) * q.1}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt (continuous_const.mul continuous_fst) continuous_snd).inter
      (isOpen_lt continuous_snd (continuous_const.mul continuous_fst)))
  have hp : p ∈ U := ⟨ha, by nlinarith [Real.pi_pos], hθ⟩
  have hc : ContDiffOn ℝ 1 (scaledMap Real.tan) U := by
    intro q hq
    have hmem : q.2 / q.1 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨(lt_div_iff₀ hq.1).mpr hq.2.1, (div_lt_iff₀ hq.1).mpr hq.2.2⟩
    exact (contDiffAt_scaledMap (ne_of_gt hq.1)
      (Real.contDiffAt_tan.mpr (Real.cos_pos_of_mem_Ioo hmem).ne')).contDiffWithinAt
  have hd : HasDerivAt Real.tan 1 0 := by simpa using Real.hasDerivAt_tan (by simp : Real.cos 0 ≠ 0)
  exact (contDiffOn_scaledClamp hU (fun q hq => ne_of_gt hq.1) hc Real.tan_zero hd).contDiffAt (hU.mem_nhds hp)

end Eden.StrangeProof.Direct
