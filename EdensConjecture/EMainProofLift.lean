import EdensConjecture.EMainProofThesis

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

abbrev LiftedX := ULift.{u} X

instance liftedInnerProductSpace : InnerProductSpace ℝ LiftedX where
  toNormedSpace := ULift.normedSpace
  inner x y := inner ℝ x.down y.down
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y r := inner_smul_left x.down y.down r

def liftIsometry : LiftedX ≃ₗᵢ[ℝ] X := LinearIsometryEquiv.ulift ℝ X

instance liftedFiniteDimensional : FiniteDimensional ℝ LiftedX :=
  FiniteDimensional.of_injective liftIsometry.toLinearEquiv.toLinearMap liftIsometry.injective

def liftOperator (A : X →L[ℝ] X) : LiftedX →L[ℝ] LiftedX :=
  liftIsometry.symm.toContinuousLinearMap.comp (A.comp liftIsometry.toContinuousLinearMap)

@[simp] lemma liftOperator_apply (A : X →L[ℝ] X) (x : LiftedX) :
    liftOperator A x = ULift.up (A x.down) := rfl

lemma continuous_liftOperator : Continuous (liftOperator : (X →L[ℝ] X) → LiftedX →L[ℝ] LiftedX) := by
  unfold liftOperator
  fun_prop

lemma norm_liftOperator (A : X →L[ℝ] X) : ‖liftOperator.{u} A‖ = ‖A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact A.le_opNorm x.down
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    exact (liftOperator.{u} A).le_opNorm (ULift.up x)

lemma liftOperator_comp (A B : X →L[ℝ] X) : liftOperator.{u} (A.comp B) = (liftOperator A).comp (liftOperator B) := by
  ext x
  rfl

def liftedSetting (D : ThesisSetting X) : ThesisSetting LiftedX.{u} where
  X := {x | x.down ∈ D.X}
  nonempty_X := by obtain ⟨x, hx⟩ := D.nonempty_X; exact ⟨ULift.up x, hx⟩
  compact_X := by
    convert D.compact_X.image liftIsometry.symm.continuous using 1
    ext x
    change x.down ∈ D.X ↔ ∃ y ∈ D.X, ULift.up y = x
    constructor
    · intro hx
      exact ⟨x.down, hx, by cases x; rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  S := fun t x => ULift.up (D.S t x.down)
  initial := fun x => by rw [D.initial]
  semigroup := fun t s ht hs x => by rw [D.semigroup t s ht hs]
  continuous_space := fun t ht => liftIsometry.symm.continuous.comp ((D.continuous_space t ht).comp liftIsometry.continuous)
  continuous_on_X := by
    have hf : Continuous (fun p : ℝ × LiftedX => (p.1, p.2.down)) := by
      exact continuous_fst.prodMk (liftIsometry.continuous.comp continuous_snd)
    exact liftIsometry.symm.continuous.comp_continuousOn
      (D.continuous_on_X.comp hf.continuousOn (fun _ hp => hp))
  invariant_X := by
    intro t ht
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hh : D.S t y.down ∈ D.X := by rw [← D.invariant_X t ht]; exact ⟨y.down, hy, rfl⟩
      change x.down ∈ D.X
      rw [← congrArg ULift.down hxy]
      exact hh
    · intro hx
      have hh : x.down ∈ D.S t '' D.X := by rw [D.invariant_X t ht]; exact hx
      obtain ⟨y, hy, hxy⟩ := hh
      exact ⟨ULift.up y, hy, by cases x; simpa using congrArg (fun z : X => (ULift.up z : LiftedX.{u})) hxy⟩
  S' := fun t x => liftOperator (D.S' t x.down)
  derivative_continuous := by
    have hf : Continuous (fun p : ℝ × LiftedX => (p.1, p.2.down)) :=
      continuous_fst.prodMk (liftIsometry.continuous.comp continuous_snd)
    exact continuous_liftOperator.comp_continuousOn
      (D.derivative_continuous.comp hf.continuousOn (fun _ hp => hp))
  derivative_injective := by
    intro t ht x hx y z hyz
    apply ULift.ext
    exact D.derivative_injective t ht x.down hx (congrArg ULift.down hyz)
  derivative_CC := fun _ _ _ _ => finiteDimensional_CC _
  derivative_cocycle := fun t s ht hs x hx => by rw [D.derivative_cocycle t s ht hs x.down hx, liftOperator_comp]
  short_time_bound := by
    obtain ⟨M, hM⟩ := D.short_time_bound
    refine ⟨M, fun t ht ht₁ x hx => ?_⟩
    rw [norm_liftOperator]
    exact hM t ht ht₁ x.down hx
  P := fun t x => liftOperator (D.P t x.down)
  positive_part := by
    intro t ht x hx
    obtain ⟨h₁, h₂, h₃⟩ := D.positive_part t ht x.down hx
    exact ⟨fun y z => h₁ y.down z.down, fun y => h₂ y.down, fun y z => h₃ y.down z.down⟩
  c := D.c
  remainder := D.remainder
  c_nonneg := D.c_nonneg
  remainder_nonneg := D.remainder_nonneg
  remainder_zero := D.remainder_zero
  remainder_small := D.remainder_small
  frechet_type_condition := fun t ht x hx y hy => D.frechet_type_condition t ht x.down hx y.down hy

lemma sNumber_liftOperator (P : X →L[ℝ] X) (hP : P.toLinearMap.IsSymmetric) (j : Fin 5) :
    sNumber (liftOperator.{u} P) (j.val + 1) = sNumber P (j.val + 1) := by
  have hn : Module.finrank ℝ X = 5 := by simp [X, PhaseSpace]
  let b := hP.eigenvectorBasis hn
  let c := hP.eigenvalues hn
  have hbase : ∀ i, P (b i) = c i • b i := hP.apply_eigenvectorBasis hn
  rw [sNumber_eq_eigenvalue b P c hbase (hP.eigenvalues_antitone hn) j]
  apply sNumber_eq_eigenvalue (b.map liftIsometry.symm) _ c _ (hP.eigenvalues_antitone hn) j
  intro i
  apply ULift.ext
  exact hbase i

lemma liftedSetting_s (D : ThesisSetting X) {t : ℝ} (ht : 0 < t) {x : LiftedX} (hx : x.down ∈ D.X)
    (j : Fin 5) : (liftedSetting D).s (j.val + 1) t x = D.s (j.val + 1) t x.down := by
  exact sNumber_liftOperator _ (D.positive_part t ht x.down hx).1 j

lemma liftedSetting_w (D : ThesisSetting X) {t : ℝ} (ht : 0 < t) {x : LiftedX} (hx : x.down ∈ D.X)
    {k : ℕ} (hk : k ≤ 5) : (liftedSetting D).w k t x = D.w k t x.down := by
  apply Finset.prod_congr rfl
  intro i hi
  exact liftedSetting_s D ht hx ⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩

lemma liftedSetting_cumulative (D : ThesisSetting X) {x : LiftedX} (hx : x.down ∈ D.X)
    {k : ℕ} (hk : k ≤ 5) : (liftedSetting D).cumulativeLocalExponent k x = D.cumulativeLocalExponent k x.down := by
  apply Filter.limsup_congr
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [liftedSetting_w D ht hx hk]

lemma liftedSetting_realSpectrum (D : ThesisSetting X) (μ : ℕ → X → ℝ)
    (hμ : D.RealLocalSpectrumThrough 4 μ) :
    (liftedSetting.{u} D).RealLocalSpectrumThrough 4 (fun i x => μ i x.down) := by
  intro x hx k hk
  rw [liftedSetting_cumulative D hx hk]
  exact hμ x.down hx k hk

lemma liftedSetting_firstIndex (D : ThesisSetting X) (μ : ℕ → X → ℝ)
    (hμ : D.FirstDimensionIndex 4 μ) :
    (liftedSetting.{u} D).FirstDimensionIndex 4 (fun i x => μ i x.down) := by
  refine ⟨fun x hx => hμ.1 x.down hx, ?_⟩
  intro m hm hneg
  exact hμ.2 m hm (fun x hx => hneg (ULift.up x) hx)

lemma liftedSetting_stationary (D : ThesisSetting X) (x : LiftedX) :
    StationarySolution (liftedSetting D).S x ↔ StationarySolution D.S x.down := by
  constructor
  · intro h t ht
    exact congrArg ULift.down (h t ht)
  · intro h t ht
    apply ULift.ext
    exact h t ht

lemma liftedSetting_periodic (D : ThesisSetting X) (x : LiftedX) :
    PeriodicSolution (liftedSetting D).S x ↔ PeriodicSolution D.S x.down := by
  constructor
  · rintro ⟨hs, t, ht, hper⟩
    refine ⟨fun h => hs ((liftedSetting_stationary D x).mpr h), t, ht, ?_⟩
    intro s hs
    exact congrArg ULift.down (hper s hs)
  · rintro ⟨hs, t, ht, hper⟩
    refine ⟨fun h => hs ((liftedSetting_stationary D x).mp h), t, ht, ?_⟩
    intro s hs
    apply ULift.ext
    exact hper s hs

lemma liftedSetting_globalAttractor (D : ThesisSetting X) (hD : D.IsGlobalAttractor) :
    (liftedSetting.{u} D).IsGlobalAttractor := by
  intro B hB ε hε
  have hB' : Bornology.IsBounded (ULift.down '' B) := liftIsometry.isometry.lipschitz.isBounded_image hB
  obtain ⟨T, hT, hbound⟩ := hD (ULift.down '' B) hB' ε hε
  refine ⟨T, hT, ?_⟩
  intro t ht x hx
  obtain ⟨y, hy, hxy⟩ := hbound t ht x.down ⟨x, hx, rfl⟩
  exact ⟨ULift.up y, hy, hxy⟩

lemma liftedSetting_dimensionExpression (D : ThesisSetting X) {t : ℝ} (ht : 0 < t)
    {x : LiftedX} (hx : x.down ∈ D.X) (d : ℝ) :
    (liftedSetting D).dimensionExpression 4 d t x = D.dimensionExpression 4 d t x.down := by
  unfold ThesisSetting.dimensionExpression
  rw [liftedSetting_w D ht hx (by norm_num), liftedSetting_s D ht hx (⟨4, by decide⟩ : Fin 5)]

lemma liftedSetting_dimensionSup (D : ThesisSetting X) {t : ℝ} (ht : 0 < t) (d : ℝ) :
    sSup ((liftedSetting.{u} D).dimensionExpression 4 d t '' (liftedSetting D).X) =
      sSup (D.dimensionExpression 4 d t '' D.X) := by
  congr 1
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.down, hx, (liftedSetting_dimensionExpression D ht hx d).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨ULift.up x, hx, liftedSetting_dimensionExpression D ht hx d⟩

lemma liftedSetting_DO (D : ThesisSetting X) :
    (liftedSetting.{u} D).douadyOesterleDimension 4 = D.douadyOesterleDimension 4 := by
  unfold ThesisSetting.douadyOesterleDimension
  congr 1
  ext a
  have he (d : ℝ) : (fun t : ℝ => sSup ((liftedSetting.{u} D).dimensionExpression 4 d t '' (liftedSetting D).X))
      =ᶠ[atTop] (fun t => sSup (D.dimensionExpression 4 d t '' D.X)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact liftedSetting_dimensionSup D ht d
  constructor
  · rintro ⟨d, hd, rfl, hlim⟩
    exact ⟨d, hd, rfl, hlim.congr' (he d)⟩
  · rintro ⟨d, hd, rfl, hlim⟩
    exact ⟨d, hd, rfl, hlim.congr' (he d).symm⟩

end Eden.PolynomialCounterexample
