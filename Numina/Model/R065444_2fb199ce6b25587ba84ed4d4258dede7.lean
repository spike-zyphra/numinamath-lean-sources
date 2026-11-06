import Mathlib

theorem algebra_194317 {x : ℝ} (hx : 3 * x ^ 4 + 13 * x ^ 3 + 20 * x ^ 2 + 17 * x + 7 = 0) :
    3 * x ^ 4 + x ^ 3 - 8 * x ^ 2 + 11 * x - 7 = 0 ↔ x = -7 / 3 := by
  constructor
  · -- Assume 3x^4 + x^3 - 8x^2 + 11x - 7 = 0, prove x = -7/3
    intro h
    have eq1 : 3 * x ^ 4 + 13 * x ^ 3 + 20 * x ^ 2 + 17 * x + 7 = 0 := hx
    have eq2 : 3 * x ^ 4 + x ^ 3 - 8 * x ^ 2 + 11 * x - 7 = 0 := by linarith
    have eq3 : 12 * x ^ 3 + 28 * x ^ 2 + 6 * x + 14 = 0 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x * x - 1 / 2), sq_nonneg (x + 7 / 3), sq_nonneg (x ^ 2 - 1 / 2)]
    have h1 : (x + 7 / 3) * (2 * x ^ 2 + 1) = 0 := by 
      nlinarith [sq_nonneg (x + 7 / 3), sq_nonneg (x ^ 2), sq_nonneg (x * 2)]
    cases' (mul_eq_zero.mp h1) with h2 h3
    · 
      linarith 
    · -- Case that 2x^2 + 1 = 0
      have h4 : x ^ 2 = -1 / 2 := by
        nlinarith 
      have h5 : x ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      nlinarith 
  · -- Assume x = -7/3, prove 3x^4 + x^3 - 8x^2 + 11x - 7 = 0
    intro h
    rw [h]
    norm_num