import Mathlib

theorem algebra_315688 {x y : ℝ} (h₀ : x^2 + Real.sqrt 3 * y = 4) (h₁ : y^2 + Real.sqrt 3 * x = 4) (h₂ : x ≠ y) :
    y / x + x / y = -5 := by
  have h3 : (x - y) * (x + y - Real.sqrt 3) = 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h₀, h₁, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - y), sq_nonneg (x + y - Real.sqrt 3)]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case where x - y = 0, which implies x = y.
    exfalso
    exact h₂ (by linarith)
  · -- Case where x + y - sqrt 3 = 0, which implies x + y = sqrt 3
    have h6 : x + y = Real.sqrt 3 := by linarith
    have h7 : x * y = -1 := by
      have h8 : x + y = Real.sqrt 3 := h6
      have h9 : (x + y) ^ 2 = 3 := by
        calc
          (x + y) ^ 2 = (Real.sqrt 3) ^ 2 := by rw [h8]
          _ = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      have h10 : x^2 + y^2 = 5 := by
        nlinarith [h₀, h₁, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h6]
      have h11 : (x + y) ^ 2 = x^2 + y^2 + 2 * (x * y) := by ring
      rw [h10] at h11
      rw [h9] at h11
      nlinarith
    have hx : x ≠ 0 := by
      by_contra h
      rw [h] at h7
      simp at h7
      all_goals linarith
    have hy : y ≠ 0 := by
      by_contra h
      rw [h] at h7
      simp at h7
      all_goals linarith
    have h8 : y / x + x / y = (y^2 + x^2) / (x * y) := by
      field_simp [hx, hy]
      <;> ring
    rw [h8]
    have h9 : y^2 + x^2 = 5 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h6, h7, h₀, h₁]
    rw [h9, h7]
    all_goals nlinarith