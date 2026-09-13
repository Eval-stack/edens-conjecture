import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section

namespace Eden.StrangeProof

open Set

/-! ## An explicit quotient model of the two-torus

Coordinates are taken modulo integer translations in each component.
No differentiable-manifold or Hausdorff-dimension result about this quotient
is being asserted here. Only the algebraic no-return obstruction is needed.
-/

/-- Equality modulo an integer in each coordinate. -/
def PhaseEquivalent (p q : ℝ × ℝ) : Prop :=
  ∃ m k : ℤ,
    q.1 = p.1 + (m : ℝ) ∧ q.2 = p.2 + (k : ℝ)

private theorem phaseEquivalent_refl (p : ℝ × ℝ) :
    PhaseEquivalent p p := by
  exact ⟨0, 0, by simp, by simp⟩

private theorem phaseEquivalent_symm {p q : ℝ × ℝ}
    (h : PhaseEquivalent p q) : PhaseEquivalent q p := by
  rcases h with ⟨m, k, hm, hk⟩
  refine ⟨-m, -k, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

private theorem phaseEquivalent_trans {p q r : ℝ × ℝ}
    (hpq : PhaseEquivalent p q) (hqr : PhaseEquivalent q r) :
    PhaseEquivalent p r := by
  rcases hpq with ⟨m, k, hm, hk⟩
  rcases hqr with ⟨a, b, ha, hb⟩
  refine ⟨m + a, k + b, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

private def phaseSetoid : Setoid (ℝ × ℝ) where
  r := PhaseEquivalent
  iseqv := ⟨phaseEquivalent_refl,
    phaseEquivalent_symm, phaseEquivalent_trans⟩

/-- The quotient ℝ²/ℤ², used here only as a type with translations. -/
def PhaseTorus := Quotient phaseSetoid

private def translatedCoordinates (α t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + t, p.2 + α * t)

private theorem translatedCoordinates_respects (α t : ℝ)
    {p q : ℝ × ℝ} (h : PhaseEquivalent p q) :
    PhaseEquivalent (translatedCoordinates α t p)
      (translatedCoordinates α t q) := by
  rcases h with ⟨m, k, hm, hk⟩
  refine ⟨m, k, ?_, ?_⟩
  · dsimp only [translatedCoordinates]
    linarith
  · dsimp only [translatedCoordinates]
    linarith

/-- Translation by (t, αt) modulo ℤ². -/
def torusTranslation (α t : ℝ) (q : PhaseTorus) : PhaseTorus :=
  Quotient.map (translatedCoordinates α t)
    (fun _ _ h => translatedCoordinates_respects α t h) q

/-- The translation family starts at the identity. -/
theorem torusTranslation_zero (α : ℝ) (q : PhaseTorus) :
    torusTranslation α 0 q = q := by
  refine Quotient.inductionOn q ?_
  intro p
  change Quotient.mk phaseSetoid (translatedCoordinates α 0 p) =
    Quotient.mk phaseSetoid p
  have hp : translatedCoordinates α 0 p = p := by
    apply Prod.ext <;> simp [translatedCoordinates]
  exact congrArg (Quotient.mk phaseSetoid) hp

/-- The translation family satisfies the flow law for all real times. -/
theorem torusTranslation_add (α t s : ℝ) (q : PhaseTorus) :
    torusTranslation α (t + s) q =
      torusTranslation α t (torusTranslation α s q) := by
  refine Quotient.inductionOn q ?_
  intro p
  change Quotient.mk phaseSetoid (translatedCoordinates α (t + s) p) =
    Quotient.mk phaseSetoid
      (translatedCoordinates α t (translatedCoordinates α s p))
  apply congrArg (Quotient.mk phaseSetoid)
  apply Prod.ext <;> dsimp [translatedCoordinates] <;> ring

/-- A positive return would make both t and αt integers. -/
theorem torusTranslation_no_positive_return
    {α t : ℝ} (hα : Irrational α) (ht : 0 < t)
    (q : PhaseTorus) : torusTranslation α t q ≠ q := by
  refine Quotient.inductionOn q ?_
  intro p hreturn
  change Quotient.mk phaseSetoid (translatedCoordinates α t p) =
    Quotient.mk phaseSetoid p at hreturn
  have hrel : PhaseEquivalent p (translatedCoordinates α t p) :=
    Quotient.exact hreturn.symm
  rcases hrel with ⟨m, k, hm, hk⟩
  dsimp only [translatedCoordinates] at hm hk
  have htm : t = (m : ℝ) := by linarith
  have hatk : α * t = (k : ℝ) := by linarith
  have hm0 : m ≠ 0 := by
    intro hmzero
    have htzero : t = 0 := by simpa [hmzero] using htm
    exact (ne_of_gt ht) htzero
  have hamk : α * (m : ℝ) = (k : ℝ) := by
    simpa only [htm] using hatk
  exact (hα.mul_intCast hm0).ne_int k hamk

/-! ## Transfer of aperiodicity through a phase factor -/

/-- No point of A returns to itself at a strictly positive time.
This excludes both stationary points and nonstationary periodic solutions. -/
def NoPositiveReturns {X : Type*} (S : ℝ → X → X) (A : Set X) : Prop :=
  ∀ p ∈ A, ∀ t : ℝ, 0 < t → S t p ≠ p

/-- A factor identity is enough to exclude periodic points. Injectivity,
surjectivity and continuity of the phase map are not needed for that logical
consequence; an actual geometric realization must still supply the identity. -/
def HasTorusTranslationFactor {X : Type*}
    (S : ℝ → X → X) (A : Set X) (α : ℝ) : Prop :=
  ∃ phase : X → PhaseTorus,
    ∀ p ∈ A, ∀ t : ℝ, 0 ≤ t →
      phase (S t p) = torusTranslation α t (phase p)

/-- A positive return in a flow induces a positive return in every factor. -/
theorem noPositiveReturns_of_torusFactor
    {X : Type*} {S : ℝ → X → X} {A : Set X} {α : ℝ}
    (hα : Irrational α) (hfactor : HasTorusTranslationFactor S A α) :
    NoPositiveReturns S A := by
  rcases hfactor with ⟨phase, hphase⟩
  intro p hp t ht hreturn
  have hphaseReturn : torusTranslation α t (phase p) = phase p := by
    calc
      torusTranslation α t (phase p) = phase (S t p) :=
        (hphase p hp t (le_of_lt ht)).symm
      _ = phase p := congrArg phase hreturn
  exact torusTranslation_no_positive_return hα ht (phase p) hphaseReturn

/-- The irrational number used in the solenoid suspension construction. -/
theorem noPositiveReturns_of_sqrtTwoFactor
    {X : Type*} {S : ℝ → X → X} {A : Set X}
    (hfactor : HasTorusTranslationFactor S A (Real.sqrt 2)) :
    NoPositiveReturns S A :=
  noPositiveReturns_of_torusFactor irrational_sqrt_two hfactor

end Eden.StrangeProof
