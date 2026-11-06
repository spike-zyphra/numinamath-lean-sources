import Mathlib

theorem algebra_357 :
    IsLeast {t : ℝ | ∃ x y, t = x ^ 2 + y ^ 2 ∧ x * y - x - y = 1} (6 - 4 * √2) := by
  constructor
  · -- First part: prove 6 - 4 * √2 is in the set.
    use 1 - Real.sqrt 2, 1 - Real.sqrt 2
    constructor
    · -- Show that (1 - √2)^2 + (1 - √2)^2 = 6 - 4 * √2
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sqrt_nonneg 2]
    · -- Show that (1 - √2)*(1 - √2) - (1 - √2) - (1 - √2) = 1
      have h1 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      nlinarith [h1, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (0 : ℝ) < (2 : ℝ)), Real.sqrt_nonneg 2]
  · -- Second part: prove that 6 - 4 * √2 is the minimum
    rintro t ⟨x, y, ht, h_eq⟩
    have h1 : x * y = x + y + 1 := by linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - (2 - 2 * Real.sqrt 2)), sq_nonneg (x - (1 - Real.sqrt 2)), sq_nonneg (y - (1 - Real.sqrt 2)), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ))]