import Mathlib

theorem inequalities_49438 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : (1 + x) * (1 + y) = 2) : 6 ≤ x * y + 1 / (x * y) := by
  have h1 : x * y > 0 := mul_pos hx hy
  have h2 : (x + y) ≥ 0 := by nlinarith
  have h3 : x + y + x * y = 1 := by nlinarith
  have h4 : (x + y) = 1 - x * y := by linarith
  have h5 : (x + y) ^ 2 ≥ 4 * (x * y) := by
    nlinarith [sq_nonneg (x - y)]
  have h6 : (x * y) + 1 / (x * y) ≥ 6 := by 
    have h7 : (x * y) + 1 / (x * y) - 6 ≥ 0 := by
      have h5' : (x * y) ^ 2 + 1 - 6 * (x * y) ≥ 0 := by
        have h2 : (x + y) ^ 2 ≥ 4 * (x * y) := by
          nlinarith [sq_nonneg (x - y)]
        rw [h4] at h2
        nlinarith
      have h8 : (x * y) + 1 / (x * y) - 6 = ((x * y) ^ 2 + 1 - 6 * (x * y)) / (x * y) := by
        field_simp [h1]
        <;> nlinarith
      rw [h8]
      apply div_nonneg
      linarith
      positivity
    nlinarith
  linarith [h6]