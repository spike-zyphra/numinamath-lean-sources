import Mathlib

theorem algebra_303086 {x y : ℝ} (h₀ : x + y = 3) (h₁ : 1 / (x + y ^ 2) + 1 / (x ^ 2 + y) = 1 / 2) :
    x ^ 5 + y ^ 5 = 123 := by
  have h2 : x + y ^ 2 ≠ 0 := by
    by_contra h
    have h3 : x = -y ^ 2 := by linarith
    have h4 : y ^ 2 - y + 3 = 0 := by
      rw [h3] at h₀
      nlinarith
    have h5 : (y - 1 / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith
  have h3 : x ^ 2 + y ≠ 0 := by
    by_contra h
    have h4 : y = -x ^ 2 := by linarith
    have h5 : x ^ 2 - x + 3 = 0 := by
      rw [h4] at h₀
      nlinarith
    have h6 : (x - 1 / 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith
  have h4 : 2 * (x ^ 2 + y + x + y ^ 2) = (x + y ^ 2) * (x ^ 2 + y) := by
    have h5 : 1 / (x + y ^ 2) + 1 / (x ^ 2 + y) = 1 / 2 := h₁
    field_simp [h2, h3] at h5 ⊢
    nlinarith
  have h4' : x ^ 2 + y ^ 2 = 9 - 2 * (x * y) := by
    have h7 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
      ring
    rw [h7, h₀]
    all_goals
      nlinarith
  have h5 : 2 * (x ^ 2 + y + x + y ^ 2) = (x + y ^ 2) * (x ^ 2 + y) := h4
  have h6 : 2 * (x ^ 2 + y + x + y ^ 2) = 24 - 4 * (x * y) := by
    have h7 : x ^ 2 + y ^ 2 = 9 - 2 * (x * y) := h4'
    have h8 : x ^ 2 + y + x + y ^ 2 = (x ^ 2 + y ^ 2) + (x + y) := by
      ring
    rw [h8, h7, h₀]
    all_goals
      nlinarith
  have h7 : (x + y ^ 2) * (x ^ 2 + y) = x^3 + y^3 + (x * y) + (x * y) ^ 2 := by
    nlinarith [sq_nonneg (x * y)]
  rw [h7] at h5
  rw [h6] at h5
  have h8 : x ^ 3 + y ^ 3 = 27 - 9 * (x * y) := by
    have h9 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x + y) * (x * y) := by
      ring
    rw [h9, h₀]
    all_goals
      nlinarith
  rw [h8] at h5
  have h9 : (x * y) ^ 2 - 4 * (x * y) + 3 = 0 := by
    nlinarith
  have h10 : (x * y - 1) * (x * y - 3) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h10) with h11 h12
  ·
    have h13 : x * y = 1 := by linarith
    have h14 : x ^ 2 + y ^ 2 = 7 := by
      nlinarith [h₀, h13]
    have h15 : x ^ 3 + y ^ 3 = 18 := by
      have h16 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x + y) * (x * y) := by
        ring
      rw [h16, h₀, h13]
      all_goals
        nlinarith
    have h17 : x ^ 4 + y ^ 4 = 47 := by
      have h18 : x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by
        ring
      rw [h18, h14, h13]
      all_goals
        nlinarith
    have h19 : x ^ 5 + y ^ 5 = 123 := by
      have h20 : x ^ 5 + y ^ 5 = (x + y) * (x ^ 4 + y ^ 4) - (x * y) * (x ^ 3 + y ^ 3) := by
        ring
      rw [h20, h₀, h13, h15, h17]
      all_goals
        nlinarith
    exact h19
  ·
    have h13 : x * y = 3 := by linarith
    have h14 : x ^ 2 + y ^ 2 = 3 := by
      nlinarith [h₀, h13]
    have h15 : (x - y) ^ 2 < 0 := by
      nlinarith [h13, h14]
    have h16 : (x - y) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith