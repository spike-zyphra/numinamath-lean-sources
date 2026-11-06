import Mathlib

theorem inequalities_323650 (a : ℝ) :
    (∀ x y : ℝ, x > 0 → y > 0 → (x + y) * (1 / x + a / y) ≥ 9) ↔ a ≥ 4 := by
  constructor
  · -- First implication: from inequality to a ≥ 4.
    intro h
    have h1 := h 1 2 (by norm_num) (by norm_num)
    norm_num at h1
    linarith
  · -- Second implication: from a ≥ 4 to inequality.
    intro ha x y hx hy
    have h1 : (x + y) * (1 / x + a / y) = 1 + a + y / x + a * x / y := by
      field_simp
      ring
    have h5 : 1 + a ≥ 5 := by linarith
    have h3 : y / x > 0 := by positivity
    have h4 : a ≥ 4 := ha
    have h6 : y / x + a * x / y ≥ 4 := by
      have h7 : y / x > 0 := h3
      have h10 : y / x + a * x / y - 4 ≥ 0 := by
        have h11 : y / x + a * x / y - 4 = (y ^ 2 - 4 * x * y + a * x ^ 2) / (x * y) := by
          field_simp
          ring
        rw [h11]
        apply div_nonneg
        · -- Show numerator is non-negative
          have h14 : y ^ 2 - 4 * x * y + a * x ^ 2 ≥ 0 := by
            nlinarith [sq_nonneg (y - 2 * x), sq_nonneg (y ^ 2 - 4 * x * y), sq_nonneg (a - 4), mul_pos hx hy, sq_nonneg (y - 2 * x), sq_nonneg (x - y)]
          linarith
        · -- Show denominator is positive
          positivity
      linarith
    linarith [h1, h5, h6]