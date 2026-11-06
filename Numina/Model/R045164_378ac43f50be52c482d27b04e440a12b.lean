import Mathlib

open Real Set

theorem algebra_211048 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = min (min (4 * x + 1) (x + 2)) (-2 * x + 4)) :
    ∃ x₀, f x₀ = 8/3 ∧ ∀ x, f x ≤ 8/3 := by

  use 2 / 3
  constructor 
  · -- Show that f(2/3) = 8/3
    rw [h₀]
    norm_num
  · -- Show that ∀ x, f x ≤ 8/3
    intro x
    rw [h₀]
    by_cases h1 : 4 * x + 1 ≤ x + 2
    · -- Case where 4x+1 ≤ x+2 (i.e., x ≤ 1/3)
      have h2 : min (4 * x + 1) (x + 2) = 4 * x + 1 := by 
        apply min_eq_left
        linarith
      rw [h2]
      by_cases h3 : 4 * x + 1 ≤ -2 * x + 4
      · -- Case where 4x+1 ≤ -2x+4 (i.e., x ≤ 1/2)
        have h4 : min (4 * x + 1) (-2 * x + 4) = 4 * x + 1 := by 
          apply min_eq_left 
          linarith 
        rw [h4] 
        linarith 
      · -- Case where -2x+4 < 4x+1 (i.e., x > 1/2) 
        have h5 : min (4 * x + 1) (-2 * x + 4) = -2 * x + 4 := by 
          apply min_eq_right 
          linarith 
        rw [h5] 
        linarith 
    · -- Case where 4x+1 > x+2 (i.e., x > 1/3)
      have h3 : min (4 * x + 1) (x + 2) = x + 2 := by 
        apply min_eq_right 
        linarith 
      rw [h3] 
      by_cases h4 : x + 2 ≤ -2 * x + 4
      · -- Case where x+2 ≤ -2x+4 (i.e., x ≤ 2/3)
        have h5 : min (x + 2) (-2 * x + 4) = x + 2 := by 
          apply min_eq_left 
          linarith 
        rw [h5] 
        linarith 
      · -- Case where x+2 > -2x+4 (i.e., x > 2/3)
        have h6 : min (x + 2) (-2 * x + 4) = -2 * x + 4 := by 
          apply min_eq_right 
          linarith 
        rw [h6] 
        linarith