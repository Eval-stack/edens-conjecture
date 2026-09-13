import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

noncomputable section
namespace Eden.StrangeProof
open Filter
open scoped Topology

/-- A local inverse Lipschitz bound rules out a kernel in a derivative. -/
theorem derivative_injective_of_inverse_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {x : E} {C : ℝ}
    (hf : HasFDerivAt f f' x)
    (hb : ∀ᶠ y in 𝓝 x, dist y x ≤ C * dist (f y) (f x)) :
    Function.Injective f' := by
  have hzero : ∀ v, f' v = 0 → v = 0 := by
    intro v hv
    have hc : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hd : HasDerivAt (fun s : ℝ => f (x + s • v)) (0 : F) 0 := by
      convert! hf.comp_hasDerivAt_of_eq 0 hc (by simp) using 1 <;> simp [hv]
    have hlim : Tendsto (fun s : ℝ => C * ‖s⁻¹ • (f (x + s • v) - f x)‖)
        (𝓝[≠] 0) (𝓝 0) := by
      simpa using hd.tendsto_slope_zero.norm.const_mul C
    have he : ∀ᶠ s in 𝓝[≠] (0 : ℝ),
        ‖v‖ ≤ C * ‖s⁻¹ • (f (x + s • v) - f x)‖ := by
      have ht : Tendsto (fun s : ℝ => x + s • v) (𝓝 0) (𝓝 x) := by
        simpa using hc.continuousAt.tendsto
      have hcomp := ht.eventually hb
      filter_upwards [hcomp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0
      have hsne : s ≠ 0 := hs0
      simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hs
      have hpos : 0 < |s| := abs_pos.mpr hsne
      have hh := (le_div_iff₀ hpos).mpr (show ‖v‖ * |s| ≤ C * ‖f (x + s • v) - f x‖ by
        simpa [mul_comm] using hs)
      simpa [norm_smul, Real.norm_eq_abs, abs_inv, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
    have hn : ‖v‖ ≤ 0 := ge_of_tendsto hlim he
    exact norm_le_zero_iff.mp hn
  intro v w hvw
  apply sub_eq_zero.mp
  exact hzero (v - w) (by simp [hvw])

end Eden.StrangeProof
