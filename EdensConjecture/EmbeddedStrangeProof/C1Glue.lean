import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

noncomputable section
namespace Eden.StrangeProof
open Set Filter
open scoped Topology

theorem hasFDerivAt_real_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {f' g' : E →L[ℝ] ℝ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) (hne : g x ≠ 0) :
    HasFDerivAt (fun y => f y / g y)
      (f x • (-((g x) ^ 2)⁻¹ • g') + (g x)⁻¹ • f') x := by
  convert! hf.mul ((hasDerivAt_inv hne).comp_hasFDerivAt x hg) using 1

theorem hasFDerivAt_ite_of_eq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {L : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f L x) (hg : HasFDerivAt g L x) (he : f x = g x)
    (P : E → Prop) [DecidablePred P] :
    HasFDerivAt (fun y => if P y then f y else g y) L x := by
  have h1 : HasFDerivWithinAt (fun y => if P y then f y else g y) L {y | P y} x := by
    apply hf.hasFDerivWithinAt.congr
    · intro y hy
      exact if_pos hy
    · by_cases h : P x <;> simp [h, he]
  have h2 : HasFDerivWithinAt (fun y => if P y then f y else g y) L {y | ¬P y} x := by
    apply hg.hasFDerivWithinAt.congr
    · intro y hy
      exact if_neg hy
    · by_cases h : P x <;> simp [h, he]
  have h := h1.union h2
  have hu : {y | P y} ∪ {y | ¬P y} = univ := by ext y; simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]; exact em _
  rw [hu, hasFDerivWithinAt_univ] at h
  exact h

theorem contDiffOn_ite_le_of_matching_derivatives
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {h : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hh : Continuous h)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (he : ∀ x ∈ U, h x = 0 → f x = g x)
    (hd : ∀ x ∈ U, h x = 0 → fderiv ℝ f x = fderiv ℝ g x) :
    ContDiffOn ℝ 1 (fun x => if h x ≤ 0 then f x else g x) U := by
  let D : E → E →L[ℝ] F := fun x => if h x ≤ 0 then fderiv ℝ f x else fderiv ℝ g x
  have hDf : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hDg : ContinuousOn (fderiv ℝ g) U := hg.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD : ContinuousOn D U := by
    rw [continuousOn_iff_continuous_restrict] at hDf hDg ⊢
    exact hDf.if_le hDg (hh.comp continuous_subtype_val) continuous_const
      (fun x hx => hd x x.property hx)
  have hder : ∀ x ∈ U, HasFDerivAt (fun y => if h y ≤ 0 then f y else g y) (D x) x := by
    intro x hx
    have hfx := ((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    have hgx := ((hg x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    rcases lt_trichotomy (h x) 0 with hlt | heq | hgt
    · have hevent : (fun y => if h y ≤ 0 then f y else g y) =ᶠ[𝓝 x] f := by
        filter_upwards [hh.continuousAt.eventually (Iio_mem_nhds hlt)] with y hy
        exact if_pos (le_of_lt hy)
      simpa only [D, if_pos hlt.le] using hfx.hasFDerivAt.congr_of_eventuallyEq hevent
    · have hg' : HasFDerivAt g (fderiv ℝ f x) x := by rw [hd x hx heq]; exact hgx.hasFDerivAt
      simpa only [D, heq, if_pos le_rfl] using
        hasFDerivAt_ite_of_eq hfx.hasFDerivAt hg' (he x hx heq) (fun y => h y ≤ 0)
    · have hevent : (fun y => if h y ≤ 0 then f y else g y) =ᶠ[𝓝 x] g := by
        filter_upwards [hh.continuousAt.eventually (Ioi_mem_nhds hgt)] with y hy
        exact if_neg (not_le.mpr hy)
      simpa only [D, if_neg (not_le.mpr hgt)] using hgx.hasFDerivAt.congr_of_eventuallyEq hevent
  intro x hx
  exact (contDiffAt_one_iff.mpr ⟨D, U, hU.mem_nhds hx, hD, hder⟩).contDiffWithinAt

end Eden.StrangeProof
