import Mathlib

theorem algebra_10648 : IsLeast {(x : ℝ) | x * |x| = 2 * x + 1} (-1) := by
  constructor
  · -- Show -1 is in the set
    norm_num
  · -- Show -1 is the smallest
    intro x hx
    have h : x * |x| = 2 * x + 1 := hx
    by_cases h1 : x ≥ 0
    · -- Case where x ≥ 0
      have h2 : |x| = x := abs_of_nonneg h1
      rw [h2] at h
      nlinarith [sq_nonneg (x - (1 + Real.sqrt 2)), sq_nonneg (x - (1 - Real.sqrt 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Case where x < 0
      have h1' : x < (0 : ℝ) := by linarith
      have h2 : |x| = -x := abs_of_neg h1'
      rw [h2] at h
      have h3 : (x + 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x + 1)]
      have h4 : x + 1 = 0 := by
        apply pow_eq_zero 
        exact h3
      linarith