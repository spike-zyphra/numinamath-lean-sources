import Mathlib

theorem inequalities_121232 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : (1 + x) * (1 + y) = 2) :
    x * y + 1 / (x * y) ≥ 6 := by
  have h1 : x * y > 0 := mul_pos hx hy
  have h2 : x + y + x * y = 1 := by
    nlinarith
  have h3 : (x * y) + 1 / (x * y) - 6 ≥ 0 := by
    have h4 : (x * y) ^ 2 - 6 * (x * y) + 1 ≥ 0 := by
      have h5 : x + y = 1 - (x * y) := by
        nlinarith
      have h6 : (x + y) ^ 2 ≥ 4 * (x * y) := by
        nlinarith [sq_nonneg (x - y)]
      rw [show x + y = 1 - (x * y) by linarith] at h6
      nlinarith
    have h7 : (x * y) + 1 / (x * y) - 6 = ((x * y) ^ 2 - 6 * (x * y) + 1) / (x * y) := by
      field_simp
      <;> ring
    rw [h7]
    apply div_nonneg
    linarith
    positivity
  linarith