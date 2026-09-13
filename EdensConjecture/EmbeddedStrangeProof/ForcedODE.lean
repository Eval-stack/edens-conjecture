import EdensConjecture.EmbeddedStrangeProof.ForcedBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

theorem hasDerivAt_glue {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (heq : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) d c := by
  have hl : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) d (Iic c) c :=
    hf.hasDerivWithinAt.congr (fun t ht => if_pos ht) (if_pos le_rfl)
  have hr : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases htc : t ≤ c
      · have : t = c := le_antisymm htc ht
        subst t
        simp [heq]
      · exact if_neg htc
    · simp [heq]
  have hu := hl.union hr
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at hu
  exact hu

theorem restoring_of_nonpos {u : ℝ} (hu : u ≤ 0) : restoring u = -u ^ 2 := by
  simp [restoring, max_eq_right (show u - 1 ≤ 0 by linarith),
    max_eq_left (show 0 ≤ -u by linarith)]

theorem hasDerivAt_negativeFlow_ode {a t v : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hv : v ≤ 0) :
    HasDerivAt (fun s => negativeFlow a s v)
      (-a ^ 2 - restoring (negativeFlow a t v)) t := by
  rw [restoring_of_nonpos (negativeFlow_nonpos ha ht hv)]
  convert hasDerivAt_negativeFlow ha ht hv using 1 <;> ring

def middleFlow (a t v : ℝ) : ℝ :=
  if t ≤ v / a ^ 2 then v - a ^ 2 * t
  else negativeFlow a (t - v / a ^ 2) 0

theorem hasDerivAt_middleFlow {a t v : ℝ} (ha : 0 < a)
    (ht : 0 ≤ t) (hv : v ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => middleFlow a s v)
      (-a ^ 2 - restoring (middleFlow a t v)) t := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hlinear (s : ℝ) : HasDerivAt (fun s => v - a ^ 2 * s) (-a ^ 2) s := by
    convert! (hasDerivAt_const s v).sub ((hasDerivAt_id s).const_mul (a ^ 2)) using 1 <;>
      simp [Pi.sub_apply]
  rcases lt_trichotomy t (v / a ^ 2) with hlt | heq | hgt
  · have hmem : v - a ^ 2 * t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · have := (le_div_iff₀ ha2).mp hlt.le
        nlinarith
      · nlinarith [mul_nonneg ha2.le ht, hv.2]
    have he : (fun s => middleFlow a s v) =ᶠ[𝓝 t] (fun s => v - a ^ 2 * s) := by
      filter_upwards [Iio_mem_nhds hlt] with s hs
      exact if_pos (le_of_lt hs)
    simpa only [middleFlow, if_pos hlt.le, restoring_of_mem hmem, sub_zero] using
      (hlinear t).congr_of_eventuallyEq he
  · subst t
    have hz : v - a ^ 2 * (v / a ^ 2) = 0 := by field_simp; ring
    have hn : HasDerivAt (fun s => negativeFlow a (s - v / a ^ 2) 0)
        (-a ^ 2) (v / a ^ 2) := by
      have hn0 : HasDerivAt (fun s => negativeFlow a s 0) (-a ^ 2)
          ((v / a ^ 2) - v / a ^ 2) := by
        simpa [negativeFlow_zero ha] using hasDerivAt_negativeFlow ha (le_refl 0) (le_refl 0)
      have h := hn0.comp (h := fun s => s - v / a ^ 2)
        (v / a ^ 2) ((hasDerivAt_id (v / a ^ 2)).sub_const (v / a ^ 2))
      convert! h using 1 <;> simp
    have hg := hasDerivAt_glue (hlinear (v / a ^ 2)) hn
      (by simp [hz, negativeFlow_zero ha])
    simpa [middleFlow, hz, restoring_of_mem (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)] using hg
  · have htime : 0 ≤ t - v / a ^ 2 := sub_nonneg.mpr hgt.le
    have hn := (hasDerivAt_negativeFlow_ode ha htime (le_refl 0)).comp t
      ((hasDerivAt_id t).sub_const (v / a ^ 2))
    have he : (fun s => middleFlow a s v) =ᶠ[𝓝 t]
        (fun s => negativeFlow a (s - v / a ^ 2) 0) := by
      filter_upwards [Ioi_mem_nhds hgt] with s hs
      exact if_neg (not_le.mpr hs)
    simpa only [middleFlow, if_neg (not_le.mpr hgt), mul_one] using
      hn.congr_of_eventuallyEq he

end Eden.StrangeProof.Direct
