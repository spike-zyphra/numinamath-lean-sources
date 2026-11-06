import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_315334 (a : ℝ) :
  ¬ (∃ x : ℝ, |x - a| + |x| < 2) ↔ a ≤ -2 ∨ a ≥ 2 := by
  constructor
  · -- Assume that there's no solution, prove $a \leq -2 \text{ or } a \geq 2$
    intro h
    by_contra h1
    push_neg at h1
    have h2 : a > -2 := by linarith
    have h3 : a < 2 := by linarith
    have h4 : ∃ x : ℝ, |x - a| + |x| < 2 := by 
      use a / 2
      have h5 : |(a / 2 : ℝ) - a| + |(a / 2 : ℝ)| < 2 := by
        have h6 : (a / 2 : ℝ) - a = -(a / 2) := by ring
        rw [h6]
        have h7 : |-(a / 2 : ℝ)| = |(a / 2 : ℝ)| := by 
          rw [abs_neg]
        rw [h7]
        have h9 : |(a / 2 : ℝ)| < 1 := by
          apply abs_lt.mpr
          constructor <;> nlinarith
        have h10 : |(a / 2 : ℝ)| + |(a / 2 : ℝ)| < 2 := by
          linarith [abs_nonneg (a / 2), h9]
        linarith
      exact h5
    exact h h4
  · -- Assume $a \leq -2$ or $a \geq 2$, prove there is no solution
    rintro (h | h)
    · -- Assume a ≤ -2
      intro h1
      rcases h1 with ⟨x, hx⟩
      have h2 : |x - a| + |x| ≥ 2 := by
        cases' abs_cases (x - a) with h1 h1 <;> 
        cases' abs_cases x with h2 h2 <;> 
        all_goals 
          nlinarith
      linarith
    · -- Assume a ≥ 2
      intro h1
      rcases h1 with ⟨x, hx⟩
      have h2 : |x - a| + |x| ≥ 2 := by
        cases' abs_cases (x - a) with h1 h1 <;> 
        cases' abs_cases x with h2 h2 <;> 
        all_goals 
          nlinarith
      linarith