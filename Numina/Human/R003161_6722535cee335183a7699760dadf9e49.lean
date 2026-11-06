import Mathlib

open MeasureTheory
open ProbabilityTheory

theorem algebra_158162 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)] 
    {X Y Z : Ω → ℝ} :
    (𝔼[Z] = 𝔼[X + 2 * Y] → 𝔼[X] = 5 → 𝔼[Y] = 3 → 𝔼[Z] = 11) ∧
    (𝔼[Z] = 𝔼[3 * X + 4 * Y] → 𝔼[X] = 2 → 𝔼[Y] = 6 → 𝔼[Z] = 30) := by
  simp
  have _lemma : ∀ F : Ω → ℝ, (𝔼[F] ≠ 0) → Integrable F ℙ := by
    intro F hF
    rw [integral_def] at hF
    simp [Real.instCompleteSpace] at hF
    rcases hF with ⟨h₁, h₂⟩
    exact h₁
  constructor
  · intro hz hx hy
    rw [hz, integral_add, integral_mul_left, hx, hy]
    norm_num
    apply _lemma
    linarith
    apply Integrable.const_mul
    apply _lemma
    linarith
  · intro hz hx hy
    rw [hz, integral_add, integral_mul_left, integral_mul_left, hx, hy]
    norm_num
    all_goals {
      apply Integrable.const_mul
      apply _lemma
      linarith
    }
