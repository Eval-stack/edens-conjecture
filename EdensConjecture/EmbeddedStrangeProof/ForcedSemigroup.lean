import EdensConjecture.EmbeddedStrangeProof.TangentODE
import EdensConjecture.EmbeddedStrangeProof.Regularity
import Mathlib.Analysis.ODE.ExistUnique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set

theorem forcedScalarFlow_semigroup {a t s v : ℝ} (ha : 0 ≤ a)
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    forcedScalarFlow a (t + s) v = forcedScalarFlow a t (forcedScalarFlow a s v) := by
  let l := min v (-a)
  let r := max v 1
  let F : ℝ → ℝ := fun z => -a ^ 2 - restoring z
  have hF : ContDiff ℝ 1 F := contDiff_const.sub contDiff_restoring
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_Icc l r) (isCompact_Icc : IsCompact (Icc l r))
  have hb {q : ℝ} (hq : 0 ≤ q) : forcedScalarFlow a q v ∈ Icc l r :=
    forcedScalarFlow_bounds ha hq
  have hb' {q : ℝ} (hq : 0 ≤ q) :
      forcedScalarFlow a q (forcedScalarFlow a s v) ∈ Icc l r := by
    have h := forcedScalarFlow_bounds (v := forcedScalarFlow a s v) ha hq
    have hstart := hb hs
    exact ⟨(le_min hstart.1 (min_le_right _ _)).trans h.1,
      h.2.trans (max_le hstart.2 (le_max_right _ _))⟩
  have hd {q : ℝ} (hq : 0 ≤ q) :
      HasDerivAt (fun q => forcedScalarFlow a (q + s) v)
        (F (forcedScalarFlow a (q + s) v)) q := by
    convert! (hasDerivAt_forcedScalarFlow ha (add_nonneg hq hs) (v := v)).comp q
      ((hasDerivAt_id q).add_const s) using 1 <;> simp [F]
  have hd' {q : ℝ} (hq : 0 ≤ q) :
      HasDerivAt (fun q => forcedScalarFlow a q (forcedScalarFlow a s v))
        (F (forcedScalarFlow a q (forcedScalarFlow a s v))) q :=
    hasDerivAt_forcedScalarFlow ha hq
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => F) (s := fun _ => Icc l r) (a := 0) (b := t)
    (fun _ _ => hK)
    (fun q hq => (hd hq.1).continuousAt.continuousWithinAt)
    (fun q hq => (hd hq.1).hasDerivWithinAt)
    (fun q hq => hb (add_nonneg hq.1 hs))
    (fun q hq => (hd' hq.1).continuousAt.continuousWithinAt)
    (fun q hq => (hd' hq.1).hasDerivWithinAt)
    (fun q hq => hb' hq.1)
    (by simp [forcedScalarFlow_zero ha])
  exact heq ⟨ht, le_rfl⟩

end Eden.StrangeProof.Direct
