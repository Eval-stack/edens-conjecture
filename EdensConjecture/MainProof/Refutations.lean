import EdensConjecture.MainProof.GlobalSpectrum
import EdensConjecture.MainProof.Lift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

noncomputable section
open Set Filter TopologicalSpace
open scoped BigOperators Topology ComplexConjugate
namespace Eden.PolynomialCounterexample
universe u

theorem thesis_global_refutation :
    ¬ (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [CompleteSpace H] [SeparableSpace H],
      ∀ D : ThesisSetting H, D.IsGlobalAttractor →
        ∀ (N : ℕ) (μ : ℕ → H → ℝ),
          D.RealLocalSpectrumThrough N μ → D.FirstDimensionIndex N μ →
          (∀ x ∈ D.X, μ (N + 1) x < 0) → D.StationaryOrPeriodicSupremumAttainment N μ) := by
  intro hall
  let D := liftedSetting.{u} globalThesisSetting
  let μ : ℕ → LiftedX.{u} → ℝ := fun i x => globalMu i x.down
  have hmax := hall LiftedX.{u} D
    (liftedSetting_globalAttractor globalThesisSetting globalThesisSetting_globalAttractor) 4 μ
    (liftedSetting_realSpectrum globalThesisSetting globalMu global_realSpectrum)
    (liftedSetting_firstIndex globalThesisSetting globalMu global_firstIndex)
    (fun x hx => by change globalMu 5 x.down < 0; rw [global_fifth_rate hx]; norm_num)
  apply no_thesis_attainment_of_gap D 4 μ (15 / 4) _ _ hmax
  · obtain ⟨x, hx⟩ := nonempty_T
    refine ⟨ULift.up x, T_subset_K hx, ?_⟩
    change 15 / 4 < globalThesisSetting.localLyapunovDimension 4 globalMu x
    rw [global_localDimension_torus hx]
    norm_num
  · intro x hx hrec
    change globalThesisSetting.localLyapunovDimension 4 globalMu x.down ≤ 15 / 4
    apply recurrent_global_localDimension hx
    exact hrec.imp (liftedSetting_stationary globalThesisSetting x).mp
      (liftedSetting_periodic globalThesisSetting x).mp

theorem thesis_question1_refutation :
    ¬ (∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [CompleteSpace H] [SeparableSpace H],
      ∀ D : ThesisSetting H, ∀ (N : ℕ) (μ : ℕ → H → ℝ),
        D.RealLocalSpectrumThrough N μ → D.FirstDimensionIndex N μ →
        (∀ x ∈ D.X, μ (N + 1) x < 0) → (∃ x : H, D.CriticalPath N μ x) →
        ∃ x : H, D.CriticalPath N μ x ∧ (StationarySolution D.S x ∨ PeriodicSolution D.S x)) := by
  intro hall
  let D := liftedSetting.{u} torusThesisSetting
  let μ : ℕ → LiftedX.{u} → ℝ := fun i x => torusMu i x.down
  have hcritical : ∃ x : LiftedX.{u}, D.CriticalPath 4 μ x := by
    obtain ⟨x, hx, hbound⟩ := torusThesisSetting_critical_exists
    refine ⟨ULift.up x, hx, ?_⟩
    change (liftedSetting torusThesisSetting).douadyOesterleDimension 4 ≤
      (torusThesisSetting.localLyapunovDimension 4 torusMu x : EReal)
    rw [liftedSetting_DO]
    exact hbound
  obtain ⟨x, hx, hrec⟩ := hall LiftedX.{u} D 4 μ
    (liftedSetting_realSpectrum torusThesisSetting torusMu torusThesisSetting_realSpectrum)
    (liftedSetting_firstIndex torusThesisSetting torusMu torusThesisSetting_firstIndex)
    (fun x hx => torusThesisSetting_fifth_negative x.down hx) hcritical
  rcases hrec with hs | hp
  · exact no_stationary_on_T hx.1 ((liftedSetting_stationary torusThesisSetting x).mp hs)
  · exact no_periodic_on_T hx.1 ((liftedSetting_periodic torusThesisSetting x).mp hp)

end Eden.PolynomialCounterexample
