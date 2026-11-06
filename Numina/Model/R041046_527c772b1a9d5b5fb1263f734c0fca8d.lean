import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20936 :
  IsLeast {z : ℝ | ∃ x y : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 ∧ z = max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y)} (4 / 9) := by 
  constructor
  · -- Show 4/9 is in the set
    use 2 / 3, 2 / 3
    norm_num [max_eq_left, max_eq_right]
  · -- Show that any element in the set is ≥ 4/9
    intro z hz
    rcases hz with ⟨x, y, hx0, hxy, hy1, heq⟩
    have h1 : max (max (x * y) (1 - x - y + x * y)) (x + y - 2 * x * y) ≥ 4 / 9 := by 
      by_cases h2 : x * y ≥ 1 - x - y + x * y 
      · -- Case 1: max (x * y) (1 - x - y + x * y) = x * y 
        have h3 : max (x * y) (1 - x - y + x * y) = x * y := by 
          apply max_eq_left 
          linarith 
        rw [h3] 
        by_cases h4 : x * y ≥ x + y - 2 * x * y 
        · -- Case 1a: max = x * y 
          have h5 : max (x * y) (x + y - 2 * x * y) = x * y := by 
            apply max_eq_left 
            linarith 
          rw [h5] 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
              mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ 1 - y by linarith), 
              mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - x by linarith)
          ]
        · -- Case 1b: max = x + y - 2 * x * y 
          have h6 : max (x * y) (x + y - 2 * x * y) = x + y - 2 * x * y := by 
            apply max_eq_right 
            linarith 
          rw [h6] 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
              mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ 1 - y by linarith), 
              mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - x by linarith)
          ]
      · -- Case 2: max (x * y) (1 - x - y + x * y) = 1 - x - y + x * y 
        have h3 : max (x * y) (1 - x - y + x * y) = 1 - x - y + x * y := by 
          apply max_eq_right 
          linarith 
        rw [h3] 
        by_cases h4 : 1 - x - y + x * y ≥ x + y - 2 * x * y 
        · -- Case 2a: max = 1 - x - y + x * y 
          have h5 : max (1 - x - y + x * y) (x + y - 2 * x * y) = 1 - x - y + x * y := by 
            apply max_eq_left 
            linarith 
          rw [h5] 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
              mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ 1 - y by linarith), 
              mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - x by linarith)
          ]
        · -- Case 2b: max = x + y - 2 * x * y 
          have h6 : max (1 - x - y + x * y) (x + y - 2 * x * y) = x + y - 2 * x * y := by 
            apply max_eq_right 
            linarith 
          rw [h6] 
          nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
              mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ 1 - y by linarith), 
              mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y - x by linarith)
          ]
    linarith [heq, h1]