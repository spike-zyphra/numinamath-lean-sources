import Mathlib

theorem algebra_251777 (x : ℝ) : abs (x - abs (4 - x)) - 2 * x = 4 ↔ x = 0 := by
  constructor
  · -- Assume abs (x - abs (4 - x)) - 2 * x = 4, prove x = 0
    intro h
    have eq1 : abs (x - abs (4 - x)) = 4 + 2 * x := by linarith
    by_cases h1 : x - abs (4 - x) ≥ 0
    · -- Case where x - abs (4 - x) ≥ 0
      rw [abs_of_nonneg h1] at eq1
      by_cases h2 : (4 - x : ℝ) ≥ 0
      · -- Case where 4 - x ≥ 0, so abs (4 - x) = 4 - x
        have h3 : abs (4 - x : ℝ) = 4 - x := by
          rw [abs_of_nonneg h2]
        rw [h3] at eq1
        linarith
      · -- Case where 4 - x < 0, so abs (4 - x) = x - 4
        have h3 : abs (4 - x : ℝ) = x - 4 := by
          rw [abs_of_neg (show (4 - x : ℝ) < 0 by linarith)]
          all_goals linarith
        rw [h3] at eq1
        linarith
    · -- Case where x - abs (4 - x) < 0
      rw [abs_of_neg (show x - abs (4 - x) < 0 by linarith)] at eq1
      by_cases h2 : (4 - x : ℝ) ≥ 0
      · -- Case where 4 - x ≥ 0, so abs (4 - x) = 4 - x
        have h3 : abs (4 - x : ℝ) = 4 - x := by
          rw [abs_of_nonneg h2]
        rw [h3] at eq1
        have hx : x = 0 := by linarith
        exact hx
      · -- Case where 4 - x < 0, so abs (4 - x) = x - 4
        have h3 : abs (4 - x : ℝ) = x - 4 := by
          rw [abs_of_neg (show (4 - x : ℝ) < 0 by linarith)]
          all_goals linarith
        rw [h3] at eq1
        linarith
  · -- Assume x = 0, prove abs (x - abs (4 - x)) - 2 * x = 4
    intro h
    rw [h]
    norm_num [abs_of_pos, abs_of_neg]