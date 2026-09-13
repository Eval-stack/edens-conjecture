import EdensConjecture.EmbeddedStrangeProof.ForcedSemigroup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Filter
open scoped Topology NNReal

def scalarPhaseBox : Set (ℝ × ℝ) := Icc 0 (1 / 2) ×ˢ Icc (-1) 2
def augmentedField (p : ℝ × ℝ) : ℝ × ℝ := (0, -p.1 ^ 2 - restoring p.2)
def augmentedFlow (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, forcedScalarFlow p.1 t p.2)

theorem contDiff_augmentedField : ContDiff ℝ 1 augmentedField := by
  exact contDiff_const.prodMk ((contDiff_fst.pow 2).neg.sub (contDiff_restoring.comp contDiff_snd))

theorem augmentedFlow_mem {p : ℝ × ℝ} (hp : p ∈ scalarPhaseBox)
    {t : ℝ} (ht : 0 ≤ t) : augmentedFlow t p ∈ scalarPhaseBox := by
  have hb := forcedScalarFlow_bounds (v := p.2) hp.1.1 ht
  exact ⟨hp.1, (le_min hp.2.1 (by linarith [hp.1.2])).trans hb.1,
    hb.2.trans (max_le hp.2.2 (by norm_num))⟩

theorem hasDerivAt_augmentedFlow {p : ℝ × ℝ} (hp : 0 ≤ p.1)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => augmentedFlow s p) (augmentedField (augmentedFlow t p)) t := by
  exact (hasDerivAt_const t p.1).prodMk (hasDerivAt_forcedScalarFlow hp ht)

theorem augmentedFlow_zero {p : ℝ × ℝ} (hp : 0 ≤ p.1) : augmentedFlow 0 p = p := by
  simp [augmentedFlow, forcedScalarFlow_zero hp]

theorem exists_augmentedFlow_dist_bound : ∃ K : ℝ≥0,
    ∀ p ∈ scalarPhaseBox, ∀ q ∈ scalarPhaseBox, ∀ t ≥ 0,
      dist (augmentedFlow t p) (augmentedFlow t q) ≤ dist p q * Real.exp (K * t) := by
  obtain ⟨K, hK⟩ := contDiff_augmentedField.contDiffOn.exists_lipschitzOnWith
    (by norm_num) ((convex_Icc (0 : ℝ) (1 / 2)).prod (convex_Icc (-1 : ℝ) 2))
    (isCompact_Icc.prod isCompact_Icc)
  refine ⟨K, ?_⟩
  intro p hp q hq t ht
  have hd := dist_le_of_trajectories_ODE_of_mem
    (v := fun _ => augmentedField) (s := fun _ => scalarPhaseBox) (a := 0) (b := t)
    (fun _ _ => hK)
    (fun s hs => (hasDerivAt_augmentedFlow hp.1.1 hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hasDerivAt_augmentedFlow hp.1.1 hs.1).hasDerivWithinAt)
    (fun s hs => augmentedFlow_mem hp hs.1)
    (fun s hs => (hasDerivAt_augmentedFlow hq.1.1 hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hasDerivAt_augmentedFlow hq.1.1 hs.1).hasDerivWithinAt)
    (fun s hs => augmentedFlow_mem hq hs.1)
    (δ := dist p q) (by rw [augmentedFlow_zero hp.1.1, augmentedFlow_zero hq.1.1])
    t ⟨ht, le_rfl⟩
  simpa using hd

theorem continuousOn_augmentedFlow :
    ContinuousOn (fun p : ℝ × (ℝ × ℝ) => augmentedFlow p.1 p.2)
      (Ici 0 ×ˢ scalarPhaseBox) := by
  obtain ⟨K, hK⟩ := exists_augmentedFlow_dist_bound
  intro p hp
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hc : ContinuousAt (fun q : ℝ × (ℝ × ℝ) =>
      dist q.2 p.2 * Real.exp (K * q.1) +
        dist (augmentedFlow q.1 p.2) (augmentedFlow p.1 p.2)) p := by
    apply ContinuousAt.add
    · fun_prop
    · exact ((hasDerivAt_augmentedFlow hp.2.1.1 hp.1).continuousAt.comp continuousAt_fst).dist continuousAt_const
  have hz : Tendsto (fun q : ℝ × (ℝ × ℝ) =>
      dist q.2 p.2 * Real.exp (K * q.1) +
        dist (augmentedFlow q.1 p.2) (augmentedFlow p.1 p.2))
      (𝓝[Ici 0 ×ˢ scalarPhaseBox] p) (𝓝 0) := by
    simpa only [ContinuousWithinAt, dist_self, zero_mul, zero_add] using
      hc.continuousWithinAt (s := Ici 0 ×ˢ scalarPhaseBox)
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) _ hz
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (dist_triangle _ (augmentedFlow q.1 p.2) _).trans
    (add_le_add (hK q.2 hq.2 p.2 hp.2 q.1 hq.1) le_rfl)

end Eden.StrangeProof.Direct
