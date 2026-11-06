import Mathlib

theorem inequalities_603145 (x y z : ℝ) (h₀ : x ≠ 1) (h₁ : y ≠ 1) (h₂ : z ≠ 1)
    (h₃ : x * y * z = 1) :
    1 ≤ x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 := by
  have h4 : x - 1 ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h5 : y - 1 ≠ 0 := by
    intro h
    apply h₁
    linarith
  have h6 : z - 1 ≠ 0 := by
    intro h
    apply h₂
    linarith
  have h7 : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1 ≥ 0 := by
    have h8 : x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1 =
        (x ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2 + y ^ 2 * (x - 1) ^ 2 * (z - 1) ^ 2 + z ^ 2 * (x - 1) ^ 2 * (y - 1) ^ 2 - (x - 1) ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2) / ((x - 1) ^ 2 * (y - 1) ^ 2 * (z - 1) ^ 2) := by
      field_simp [(show x - 1 ≠ 0 by assumption), (show y - 1 ≠ 0 by assumption), (show z - 1 ≠ 0 by assumption)]
      <;> ring
    rw [h8] at *
    apply div_nonneg
    · -- Numerator is non-negative
      have h9 : x * y * z = 1 := h₃
      nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
          sq_nonneg (x + y + z - 3), sq_nonneg (x * y + y * z + z * x - 3),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          h₃]
    · -- Denominator is non-negative
      positivity
  linarith