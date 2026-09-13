import EdensConjecture.EmbeddedStrangeProof.Regularity
import EdensConjecture.EmbeddedStrangeProof.DimensionLower
import EdensConjecture.EmbeddedStrangeProof.ProductCover

noncomputable section
namespace Eden.StrangeProof.Direct
open Set Eden.TorusCounterexample

def graphParameterization (p : Fin 3 → ℝ) : Eden.PhaseSpace 4 :=
  pack (((2 + p 0 : ℝ) : ℂ) * Complex.exp ((p 1 : ℂ) * Complex.I))
    (((2 - gapFunction (p 0) : ℝ) : ℂ) * Complex.exp ((p 2 : ℂ) * Complex.I))

theorem contDiff_graphParameterization : ContDiff ℝ 1 graphParameterization := by
  have hg : ContDiff ℝ 1 (fun p : Fin 3 → ℝ => gapFunction (p 0)) :=
    contDiff_gapFunction.comp (by fun_prop)
  have hp : ContDiff ℝ 1 (fun p : Fin 3 → ℝ =>
      (Complex.ofRealCLM (2 + p 0) * Complex.exp (Complex.ofRealCLM (p 1) * Complex.I),
        Complex.ofRealCLM (2 - gapFunction (p 0)) * Complex.exp (Complex.ofRealCLM (p 2) * Complex.I))) := by
    fun_prop
  exact (contDiff_pack.of_le (by simp)).comp hp

def directGraph : Set (Eden.PhaseSpace 4) :=
  radialCoordinates ⁻¹' ((fun x : ℝ => (x, -gapFunction x)) '' Icc 0 1)

theorem directGraph_subset_range : directGraph ⊆ range graphParameterization := by
  intro u hu
  obtain ⟨x, hx, he⟩ := hu
  have h1 : ‖fstC u‖ = 2 + x := by
    have h := congrArg Prod.fst he
    change x = ‖fstC u‖ - 2 at h
    linarith
  have h2 : ‖sndC u‖ = 2 - gapFunction x := by
    have h := congrArg Prod.snd he
    change -gapFunction x = ‖sndC u‖ - 2 at h
    linarith
  refine ⟨![x, Complex.arg (fstC u), Complex.arg (sndC u)], ?_⟩
  change pack (((2 + x : ℝ) : ℂ) * Complex.exp ((Complex.arg (fstC u) : ℂ) * Complex.I))
    (((2 - gapFunction x : ℝ) : ℂ) * Complex.exp ((Complex.arg (sndC u) : ℂ) * Complex.I)) = u
  rw [← h1, ← h2, Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I, pack_fstC_sndC]

theorem directGraph_dimH_upper : dimH directGraph ≤ (3 : ENNReal) := by
  have h := (dimH_mono directGraph_subset_range).trans contDiff_graphParameterization.dimH_range_le
  simpa using h

theorem directAttractor_eq_graph_union_teeth : directAttractor = directGraph ∪ teeth := rfl

theorem directAttractor_dimH_eq_max :
    dimH directAttractor = max (dimH directGraph) (dimH teeth) := by
  rw [directAttractor_eq_graph_union_teeth, dimH_union]

def unitArgument (z : ℂ) : ℝ := (Complex.arg z + Real.pi) / (2 * Real.pi)

theorem unitArgument_mem (z : ℂ) : unitArgument z ∈ Icc (0 : ℝ) 1 := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  constructor
  · exact div_nonneg (by linarith [Complex.neg_pi_lt_arg z]) hpi.le
  · apply (div_le_one hpi).mpr
    linarith [Complex.arg_le_pi z]

theorem unitArgument_angle (z : ℂ) : 2 * Real.pi * unitArgument z - Real.pi = Complex.arg z := by
  unfold unitArgument
  field_simp [Real.pi_ne_zero]
  <;> ring

def teethParameterization (p : Fin 4 → ℝ) : Eden.PhaseSpace 4 :=
  pack (((2 + p 0 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * p 2 - Real.pi : ℝ) : ℂ) * Complex.I))
    (((2 + p 1 : ℝ) : ℂ) * Complex.exp (((2 * Real.pi * p 3 - Real.pi : ℝ) : ℂ) * Complex.I))

theorem contDiff_teethParameterization : ContDiff ℝ 1 teethParameterization := by
  have hp : ContDiff ℝ 1 (fun p : Fin 4 → ℝ =>
      (Complex.ofRealCLM (2 + p 0) * Complex.exp (Complex.ofRealCLM (2 * Real.pi * p 2 - Real.pi) * Complex.I),
        Complex.ofRealCLM (2 + p 1) * Complex.exp (Complex.ofRealCLM (2 * Real.pi * p 3 - Real.pi) * Complex.I))) := by
    fun_prop
  exact (contDiff_pack.of_le (by simp)).comp hp

theorem teeth_subset_parameterization_image : teeth ⊆ teethParameterization '' teethCube := by
  intro u hu
  refine ⟨![‖fstC u‖ - 2, ‖sndC u‖ - 2, unitArgument (fstC u), unitArgument (sndC u)], ?_, ?_⟩
  · intro i hi
    fin_cases i
    · exact hu.1
    · exact hu.2
    · exact unitArgument_mem (fstC u)
    · exact unitArgument_mem (sndC u)
  · simp [teethParameterization, unitArgument_angle, Complex.norm_mul_exp_arg_mul_I]

theorem teeth_dimH_upper : dimH teeth ≤ (23 : ENNReal) / 6 := by
  exact (dimH_mono teeth_subset_parameterization_image).trans
    ((contDiff_teethParameterization.contDiffOn.dimH_image_le convex_univ (subset_univ teethCube)).trans
      teethCube_dimH_upper)

theorem directAttractor_dimH_upper : dimH directAttractor ≤ (23 : ENNReal) / 6 := by
  rw [directAttractor_dimH_eq_max]
  have h3 : (3 : ENNReal) ≤ 23 / 6 := by
    apply (ENNReal.le_div_iff_mul_le (by simp) (by simp)).mpr
    norm_num
  exact max_le (directGraph_dimH_upper.trans h3) teeth_dimH_upper

end Eden.StrangeProof.Direct
