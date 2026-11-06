import Mathlib

theorem algebra_278380 {x y : ℝ} (h₀ : y^2 = x^3 - 3 * x^2 + 2 * x) (h₁ : x^2 = y^3 - 3 * y^2 + 2 * y) :
    (x = 0 ∧ y = 0) ∨ (x = 2 + Real.sqrt 2 ∧ y = 2 + Real.sqrt 2) ∨ (x = 2 - Real.sqrt 2 ∧ y = 2 - Real.sqrt 2) := by
  have h2 : (y - x) * (y^2 + y * x + x^2 - 2 * (x + y) + 2) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y), sq_nonneg (x + y - 2)]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case y = x, so $y^2 = x^2$ and $x^2 = y^2$
    have hy : y = x := by linarith
    rw [show y = x by linarith] at h₀
    have h3 : x * (x^2 - 4 * x + 2) = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 0)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case x = 0
      left
      have h4' : x = 0 := by linarith
      have h5' : y = 0 := by linarith [h4']
      exact ⟨h4', h5'⟩
    · -- Case x^2 - 4 * x + 2 = 0
      have h6 : x^2 - 4 * x + 2 = 0 := by nlinarith
      have h7 : (x - (2 + Real.sqrt 2)) * (x - (2 - Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case x = 2 + Real.sqrt 2
        have h8' : x = 2 + Real.sqrt 2 := by linarith
        have h9' : y = 2 + Real.sqrt 2 := by linarith [h8']
        right
        left
        exact ⟨h8', h9'⟩
      · -- Case x = 2 - Real.sqrt 2
        have h9' : x = 2 - Real.sqrt 2 := by linarith
        have h10' : y = 2 - Real.sqrt 2 := by linarith [h9']
        right
        right
        exact ⟨h9', h10'⟩
  · -- Case y^2 + y * x + x^2 - 2 * (x + y) + 2 = 0
    nlinarith [sq_nonneg (y - x), sq_nonneg (y - (2 - x)), sq_nonneg (y - (2 - Real.sqrt 2)), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg ((x - 2) - (y - 2)), sq_nonneg ((y - x) ^ 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]