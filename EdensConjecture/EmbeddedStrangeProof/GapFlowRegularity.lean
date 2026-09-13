import EdensConjecture.EmbeddedStrangeProof.ZeroTransition
import EdensConjecture.EmbeddedStrangeProof.UpperRegularity
import EdensConjecture.EmbeddedStrangeProof.FlatParameter
import EdensConjecture.EmbeddedStrangeProof.FlowVariation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology

def gapFlow (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1, forcedScalarFlow (gapFunction p.1) t p.2)
def gapField (p : ℝ × ℝ) : ℝ × ℝ := (0, -gapFunction p.1 ^ 2 - restoring p.2)
def scalarStrip : Set (ℝ × ℝ) := {p | -1 < p.2 ∧ p.2 < 2}

theorem isOpen_scalarStrip : IsOpen scalarStrip :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

theorem contDiff_gapField : ContDiff ℝ 1 gapField :=
  contDiff_const.prodMk ((((contDiff_gapFunction.comp contDiff_fst).pow 2).neg).sub
    (contDiff_restoring.comp contDiff_snd))

theorem hasDerivAt_restoring_of_mem {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    HasDerivAt restoring 0 v := by
  have h := ((hasDerivAt_positiveSquare (v - 1)).comp v ((hasDerivAt_id v).sub_const 1)).sub
    ((hasDerivAt_positiveSquare (-v)).comp v (hasDerivAt_id v).neg)
  simp only [max_eq_right (sub_nonpos.mpr hv.2), max_eq_right (neg_nonpos.mpr hv.1),
    mul_zero, zero_mul, sub_zero] at h
  convert! h using 1

theorem hasDerivAt_scalarFlow_of_mem {t v : ℝ} (ht : 0 ≤ t) (hv : v ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (scalarFlow t) 1 v := by
  have hd := ((contDiff_scalarFlow ht).differentiable (by norm_num) v).hasDerivAt
  have hw : HasDerivWithinAt (scalarFlow t) 1 (Icc (0 : ℝ) 1) v := by
    apply (hasDerivAt_id v).hasDerivWithinAt.congr
    · intro y hy
      exact scalarFlow_fixed hy t
    · exact scalarFlow_fixed hv t
  have he := hd.differentiableAt.derivWithin (uniqueDiffOn_Icc_zero_one v hv)
  have he' := hw.derivWithin (uniqueDiffOn_Icc_zero_one v hv)
  rw [he] at he'
  rwa [he'] at hd

theorem gapField_fderiv_zero {p : ℝ × ℝ} (hg : gapFunction p.1 = 0)
    (hv : p.2 ∈ Icc (0 : ℝ) 1) : fderiv ℝ gapField p = 0 := by
  have hgap := (hasDerivAt_gapFunction_zero hg).comp_hasFDerivAt p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hr := (hasDerivAt_restoring_of_mem hv).comp_hasFDerivAt p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hh := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).prodMk ((hgap.pow 2).neg.sub hr)
  have h : HasFDerivAt gapField (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    simp [hg] at hh
    convert! hh using 1
  exact h.fderiv

theorem hasFDerivAt_gapFlow_flat {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ}
    (hg : gapFunction p.1 = 0) (hv : p.2 ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (gapFlow t) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) p := by
  have hy := hasFDerivAt_forcedScalarFlow_zero_parameter ht hg (by linarith [hv.1]) (by linarith [hv.2])
  have hs := (hasDerivAt_scalarFlow_of_mem ht hv).comp_hasFDerivAt p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  simp only [one_smul, Function.comp_def] at hs
  rw [hs.fderiv] at hy
  convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hy using 1

theorem contDiffAt_gapFlow_nonflat {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ}
    (h : ¬(gapFunction p.1 = 0 ∧ (p.2 = 0 ∨ p.2 = 1))) : ContDiffAt ℝ 1 (gapFlow t) p := by
  apply contDiffAt_fst.prodMk
  by_cases hn : p.2 < 0
  · exact contDiffAt_forcedScalarFlow_negative ht hn
  by_cases hg : gapFunction p.1 = 0
  · have hv0 : 0 < p.2 := lt_of_le_of_ne (le_of_not_gt hn) (by intro he; exact h ⟨hg, Or.inl he.symm⟩)
    by_cases hv1 : p.2 < 1
    · exact contDiffAt_forcedScalarFlow_middle hv0 hv1 (by simpa [hg] using hv0)
    · exact contDiffAt_forcedScalarFlow_upper_zero ht
        (lt_of_le_of_ne (le_of_not_gt hv1) (by intro he; exact h ⟨hg, Or.inr he.symm⟩)) hg
  · have ha : 0 < gapFunction p.1 := lt_of_le_of_ne (gapFunction_nonneg p.1) (Ne.symm hg)
    have hparam : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => (gapFunction q.1, q.2)) p :=
      (contDiff_gapFunction.contDiffAt.comp p contDiffAt_fst).prodMk contDiffAt_snd
    by_cases hv : p.2 = 0
    · have hc := contDiffAt_forcedScalarFlow_positive_parameter_zero_initial ha ht
      rw [← hv] at hc
      exact hc.comp p hparam
    · exact (contDiffAt_forcedScalarFlow_positive_parameter_positive_initial ht
        (p := (gapFunction p.1, p.2)) ha (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hv))).comp p hparam

theorem differentiableAt_gapFlow {t : ℝ} (ht : 0 ≤ t) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (gapFlow t) p := by
  by_cases h : gapFunction p.1 = 0 ∧ (p.2 = 0 ∨ p.2 = 1)
  · exact (hasFDerivAt_gapFlow_flat ht h.1 (by rcases h.2 with h | h <;> simp [h])).differentiableAt
  · exact (contDiffAt_gapFlow_nonflat ht h).differentiableAt (by norm_num)

theorem continuousOn_gapFlow :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => gapFlow p.1 p.2) (Ici 0 ×ˢ scalarStrip) := by
  intro p hp
  apply ContinuousWithinAt.prodMk (continuousAt_snd.fst.continuousWithinAt)
  have hmap : MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.1, (gapFunction q.2.1, q.2.2)))
      (Ici 0 ×ˢ scalarStrip) (Ici 0 ×ˢ scalarPhaseBox) := by
    intro q hq
    exact ⟨hq.1, ⟨gapFunction_nonneg _, (gapFunction_le _).trans (by norm_num)⟩, hq.2.1.le, hq.2.2.le⟩
  have hc : ContinuousWithinAt (fun r : ℝ × (ℝ × ℝ) => augmentedFlow r.1 r.2)
      (Ici 0 ×ˢ scalarPhaseBox) (p.1, (gapFunction p.2.1, p.2.2)) :=
    continuousOn_augmentedFlow _ (hmap hp)
  have hi : ContinuousAt (fun q : ℝ × (ℝ × ℝ) => (q.1, (gapFunction q.2.1, q.2.2))) p := by
    exact continuousAt_fst.prodMk ((continuous_gapFunction.continuousAt.comp continuousAt_snd.fst).prodMk continuousAt_snd.snd)
  exact (hc.comp (f := fun q : ℝ × (ℝ × ℝ) => (q.1, (gapFunction q.2.1, q.2.2)))
    hi.continuousWithinAt hmap).snd

theorem continuousAt_fderiv_gapFlow {t : ℝ} (ht : 0 ≤ t) {p : ℝ × ℝ} (hp : p ∈ scalarStrip) :
    ContinuousAt (fderiv ℝ (gapFlow t)) p := by
  by_cases h : gapFunction p.1 = 0 ∧ (p.2 = 0 ∨ p.2 = 1)
  · have hv : p.2 ∈ Icc (0 : ℝ) 1 := by rcases h.2 with h | h <;> simp [h]
    apply Eden.StrangeProof.continuousAt_fderiv_flow_of_flat_field ht isOpen_scalarStrip hp
      contDiff_gapField.contDiffAt (gapField_fderiv_zero h.1 hv)
      (continuousOn_gapFlow.mono (fun q hq => ⟨hq.1.1, hq.2⟩))
    · intro s hs
      simp [gapFlow, forcedScalarFlow, h.1, scalarFlow_fixed hv]
    · intro q hq
      simp [gapFlow, forcedScalarFlow_zero (gapFunction_nonneg _)]
    · intro q hq s hs
      exact (hasDerivAt_const s q.1).prodMk (hasDerivAt_forcedScalarFlow (gapFunction_nonneg _) hs.1)
    · exact Eventually.of_forall (differentiableAt_gapFlow ht)
    · exact hasFDerivAt_gapFlow_flat ht h.1 hv
  · exact (contDiffAt_gapFlow_nonflat ht h).continuousAt_fderiv (by norm_num)

theorem contDiffOn_gapFlow {t : ℝ} (ht : 0 ≤ t) : ContDiffOn ℝ 1 (gapFlow t) scalarStrip := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_one_iff.mpr
  exact ⟨fderiv ℝ (gapFlow t), scalarStrip, isOpen_scalarStrip.mem_nhds hp,
    fun q hq => (continuousAt_fderiv_gapFlow ht hq).continuousWithinAt,
    fun q hq => (differentiableAt_gapFlow ht q).hasFDerivAt⟩

end Eden.StrangeProof.Direct
