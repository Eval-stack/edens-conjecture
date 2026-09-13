import EdensConjecture.EStatementDefinitions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace Eden.PolynomialCounterexample

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] {n : ℕ}

def initialSpan (b : OrthonormalBasis (Fin n) ℝ H) (k : ℕ) (hk : k ≤ n) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun i : Fin k => b (i.castLE hk)))

lemma finrank_initialSpan (b : OrthonormalBasis (Fin n) ℝ H) (k : ℕ) (hk : k ≤ n) :
    Module.finrank ℝ (initialSpan b k hk) = k := by
  rw [initialSpan, finrank_span_eq_card]
  · simp
  · exact b.toBasis.linearIndependent.comp _ (Fin.castLE_injective hk)

lemma inner_initialSpan_zero (b : OrthonormalBasis (Fin n) ℝ H) (k : ℕ) (hk : k ≤ n)
    {x : H} (hx : x ∈ initialSpan b k hk) {i : Fin n} (hi : k ≤ i.val) :
    inner ℝ (b i) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    have hne : i ≠ j.castLE hk := by intro h; have := congrArg Fin.val h; simp at this; omega
    exact b.orthonormal.inner_eq_zero hne
  | zero => simp
  | add x y hx hy hix hiy => simp [inner_add_right, hix, hiy]
  | smul a x hx hix => simp [inner_smul_right, hix]

lemma basis_mem_initialSpan (b : OrthonormalBasis (Fin n) ℝ H) (k : ℕ) (hk : k ≤ n)
    (i : Fin n) (hi : i.val < k) : b i ∈ initialSpan b k hk := by
  apply Submodule.subset_span
  exact ⟨⟨i.val, hi⟩, rfl⟩

lemma unit_in_initialSpan_orthogonal (b : OrthonormalBasis (Fin n) ℝ H)
    (j : Fin n) (F : Submodule ℝ H) (hF : Module.finrank ℝ F ≤ j.val) :
    ∃ x : H, ‖x‖ = 1 ∧ x ∈ initialSpan b (j.val + 1) j.isLt ∧ x ∈ Fᗮ := by
  let E := initialSpan b (j.val + 1) j.isLt
  have hE : Module.finrank ℝ E = j.val + 1 := finrank_initialSpan b _ _
  have hn : E ⊓ Fᗮ ≠ ⊥ := by
    intro hz
    have hd := Submodule.finrank_sup_add_finrank_inf_eq E Fᗮ
    have hf := F.finrank_add_finrank_orthogonal
    have he := Submodule.finrank_le (E ⊔ Fᗮ)
    have hzero : Module.finrank ℝ ↥(E ⊓ Fᗮ) = 0 := by rw [hz]; exact finrank_bot ℝ H
    rw [hzero] at hd
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  refine ⟨‖v‖⁻¹ • v, ?_, E.smul_mem _ hv.1, Fᗮ.smul_mem _ hv.2⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]

def rayleighSet (P : H →L[ℝ] H) (F : Submodule ℝ H) : Set ℝ :=
  {a | ∃ x : H, ‖x‖ = 1 ∧ (∀ v ∈ F, inner ℝ x v = 0) ∧ a = inner ℝ (P x) x}

lemma rayleighSet_bddAbove (P : H →L[ℝ] H) (F : Submodule ℝ H) :
    BddAbove (rayleighSet P F) := by
  refine ⟨‖P‖, ?_⟩
  rintro a ⟨x, hx, _, rfl⟩
  calc
    inner ℝ (P x) x ≤ ‖P x‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ ‖P‖ := by simpa [hx] using P.le_opNorm x

lemma eigen_rayleigh (b : OrthonormalBasis (Fin n) ℝ H) (P : H →L[ℝ] H)
    (c : Fin n → ℝ) (hc : ∀ i, P (b i) = c i • b i) (x : H) :
    inner ℝ (P x) x = ∑ i, c i * (inner ℝ (b i) x) ^ 2 := by
  calc
    inner ℝ (P x) x = inner ℝ (P (∑ i, b.repr x i • b i)) x := by rw [b.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, hc, OrthonormalBasis.repr_apply_apply,
        sum_inner, inner_smul_left, RCLike.conj_to_real]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma sNumber_eq_eigenvalue (b : OrthonormalBasis (Fin n) ℝ H) (P : H →L[ℝ] H)
    (c : Fin n → ℝ) (hc : ∀ i, P (b i) = c i • b i) (hmono : Antitone c)
    (j : Fin n) : sNumber P (j.val + 1) = c j := by
  let A : Set ℝ := {a | ∃ F : Submodule ℝ H, FiniteDimensional ℝ F ∧
    Module.finrank ℝ F ≤ j.val ∧ a = sSup (rayleighSet P F)}
  have hlow : ∀ a ∈ A, c j ≤ a := by
    rintro a ⟨F, _, hF, rfl⟩
    obtain ⟨x, hx, hE, horth⟩ := unit_in_initialSpan_orthogonal b j F hF
    have hR : inner ℝ (P x) x ∈ rayleighSet P F := by
      refine ⟨x, hx, ?_, rfl⟩
      intro v hv
      exact (F.mem_orthogonal' x).mp horth v hv
    apply le_trans _ (le_csSup (rayleighSet_bddAbove P F) hR)
    rw [eigen_rayleigh b P c hc]
    calc
      c j = ∑ i, c j * (inner ℝ (b i) x) ^ 2 := by rw [← Finset.mul_sum, b.sum_sq_inner_right, hx]; ring
      _ ≤ ∑ i, c i * (inner ℝ (b i) x) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hij : i ≤ j
        · exact mul_le_mul_of_nonneg_right (hmono hij) (sq_nonneg _)
        · rw [inner_initialSpan_zero b _ _ hE (by omega)]
          simp
  let F := initialSpan b j.val (Nat.le_of_lt j.isLt)
  have hupper : sSup (rayleighSet P F) ≤ c j := by
    have hmem : inner ℝ (P (b j)) (b j) ∈ rayleighSet P F := by
      refine ⟨b j, b.orthonormal.norm_eq_one j, ?_, rfl⟩
      intro v hv
      exact inner_initialSpan_zero b _ _ hv le_rfl
    apply csSup_le ⟨_, hmem⟩
    rintro a ⟨x, hx, horth, rfl⟩
    rw [eigen_rayleigh b P c hc]
    calc
      (∑ i, c i * (inner ℝ (b i) x) ^ 2) ≤ ∑ i, c j * (inner ℝ (b i) x) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hij : j ≤ i
        · exact mul_le_mul_of_nonneg_right (hmono hij) (sq_nonneg _)
        · have hz : inner ℝ (b i) x = 0 := by
            rw [real_inner_comm]
            exact horth _ (basis_mem_initialSpan b _ _ i (by omega))
          rw [hz]
          simp
      _ = c j := by rw [← Finset.mul_sum, b.sum_sq_inner_right, hx]; ring
  have hFA : sSup (rayleighSet P F) ∈ A :=
    ⟨F, inferInstance, (finrank_initialSpan b _ _).le, rfl⟩
  change sInf A = c j
  apply le_antisymm
  · exact (csInf_le ⟨c j, hlow⟩ hFA).trans hupper
  · exact le_csInf ⟨_, hFA⟩ hlow

def basisMultiplier (b : OrthonormalBasis (Fin n) ℝ H) (c : Fin n → ℝ) : H →L[ℝ] H :=
  (b.toBasis.constr ℝ (fun i => c i • b i)).toContinuousLinearMap

lemma basisMultiplier_basis (b : OrthonormalBasis (Fin n) ℝ H) (c : Fin n → ℝ) (i : Fin n) :
    basisMultiplier b c (b i) = c i • b i := by
  exact b.toBasis.constr_basis ℝ _ i

lemma basisMultiplier_inner (b : OrthonormalBasis (Fin n) ℝ H) (c : Fin n → ℝ) (x y : H) :
    inner ℝ (basisMultiplier b c x) y =
      ∑ i, c i * inner ℝ (b i) x * inner ℝ (b i) y := by
  calc
    _ = inner ℝ (basisMultiplier b c (∑ i, b.repr x i • b i)) y := by rw [b.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, basisMultiplier_basis, OrthonormalBasis.repr_apply_apply,
        sum_inner, inner_smul_left, RCLike.conj_to_real]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma basisMultiplier_symmetric (b : OrthonormalBasis (Fin n) ℝ H) (c : Fin n → ℝ) (x y : H) :
    inner ℝ (basisMultiplier b c x) y = inner ℝ x (basisMultiplier b c y) := by
  rw [real_inner_comm (basisMultiplier b c y) x, basisMultiplier_inner, basisMultiplier_inner]
  apply Finset.sum_congr rfl
  intro i _
  ring

def operatorPositivePart (A : H →L[ℝ] H) : H →L[ℝ] H :=
  basisMultiplier (A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
    (fun i => A.toLinearMap.singularValues i)

lemma operatorPositivePart_spec (A : H →L[ℝ] H) : PositivePart A (operatorPositivePart A) := by
  let b := A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let c : Fin (Module.finrank ℝ H) → ℝ := fun i => A.toLinearMap.singularValues i
  change PositivePart A (basisMultiplier b c)
  refine ⟨basisMultiplier_symmetric b c, ?_, ?_⟩
  · intro x
    rw [eigen_rayleigh b _ c (basisMultiplier_basis b c)]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (A.toLinearMap.singularValues_nonneg i) (sq_nonneg _)
  · have hsquare : (basisMultiplier b c).toLinearMap.comp (basisMultiplier b c).toLinearMap =
        A.toLinearMap.adjoint.comp A.toLinearMap := by
      apply b.toBasis.ext
      intro i
      simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
        ContinuousLinearMap.coe_coe, basisMultiplier_basis, map_smul, smul_smul]
      change (c i * c i) • b i = (A.toLinearMap.adjoint.comp A.toLinearMap) (b i)
      rw [← sq, A.toLinearMap.sq_singularValues_fin rfl,
        A.toLinearMap.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i]
      rfl
    intro x y
    rw [basisMultiplier_symmetric]
    have hxy := congrArg (fun L : H →ₗ[ℝ] H => inner ℝ x (L y)) hsquare
    change inner ℝ x (basisMultiplier b c (basisMultiplier b c y)) = _ at hxy
    rw [hxy]
    exact LinearMap.adjoint_inner_right A.toLinearMap x (A y)

lemma sNumber_operatorPositivePart (A : H →L[ℝ] H) (j : Fin (Module.finrank ℝ H)) :
    sNumber (operatorPositivePart A) (j.val + 1) = A.toLinearMap.singularValues j := by
  apply sNumber_eq_eigenvalue
    (A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl) _
    (fun i => A.toLinearMap.singularValues i) _ _ j
  · exact basisMultiplier_basis _ _
  · intro i k hik
    exact A.toLinearMap.singularValues_antitone hik

end Eden.PolynomialCounterexample
