import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_90523 {M : ℝ → ℝ → ℝ}
  (hM : M = λ a b => max (3 * a ^ 2 + 2 * b) (3 * b ^ 2 + 2 * a)) :
  IsLeast {x | ∃ a b, x = M a b} (M (-1 / 3) (-1 / 3)) := by
  have h1 : ∀ a b, M a b = max (3 * a ^ 2 + 2 * b) (3 * b ^ 2 + 2 * a) := by
    intro a b
    rw [hM]

  have h2 : M (-1 / 3) (-1 / 3) = -1 / 3 := by
    rw [h1]
    norm_num [max_eq_left, max_eq_right]
    <;> norm_num <;> linarith
  constructor
  · -- Show that M (-1/3, -1/3) is in the image
    use -1 / 3, -1 / 3
    all_goals linarith [h2]

  · -- Show that M (-1/3, -1/3) is the least in the image
    intro x hx
    rcases hx with ⟨a, b, h⟩
    have hx' : x = max (3 * a ^ 2 + 2 * b) (3 * b ^ 2 + 2 * a) := by 
      rw [h1] at h 
      linarith
    rw [h2] at *
  
    have h3 : max (3 * a ^ 2 + 2 * b) (3 * b ^ 2 + 2 * a) ≥ -1 / 3 := by
      by_cases h4 : (3 * a ^ 2 + 2 * b) ≥ (3 * b ^ 2 + 2 * a)
      · -- Case 1: when $3a^2+2b \ge 3b^2+2a$
        rw [max_eq_left h4]
        nlinarith [sq_nonneg (a - (-1/3)), sq_nonneg (b - (-1/3)), sq_nonneg (a - b), sq_nonneg (a + 1/3 - (b + 1/3)), 
          mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)]
      · -- Case 2: when $3b^2+2a > 3a^2+2b$
        rw [max_eq_right (by linarith)]
        nlinarith [sq_nonneg (a - (-1/3)), sq_nonneg (b - (-1/3)), sq_nonneg (a - b), sq_nonneg (a + 1/3 - (b + 1/3)), 
          mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num), 
          sq_nonneg (3 * (a + 1 / 3) - 2 * (b + 1 / 3)), 
          sq_nonneg (3 * (b + 1 / 3) - 2 * (a + 1 / 3)), 
          mul_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)]

    linarith [h3, hx']