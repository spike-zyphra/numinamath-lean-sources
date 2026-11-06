import Mathlib

theorem inequalities_30808 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (1 + x / y) ^ 3 + (1 + y / x) ^ 3 ≥ 16 := by
  have h1 : 0 < y := hy
  have h2 : 0 < x := hx
  have h3 : x / y + y / x ≥ 2 := by
    have h4 : x / y + y / x - 2 ≥ 0 := by
      have h5 : x / y + y / x - 2 = (x^2 + y^2 - 2 * x * y) / (y * x) := by
        field_simp
        <;> ring
      rw [h5]
      have h6 : x^2 + y^2 - 2 * x * y ≥ 0 := by 
        nlinarith [sq_nonneg (x - y)]
      have h7 : y * x > 0 := mul_pos hy hx
      apply div_nonneg
      . linarith
      . positivity
    linarith
  have h4 : (1 + x / y) + (1 + y / x) = 2 + (x / y + y / x) := by 
    field_simp
    <;> ring
  have h5 : (1 + x / y) * (1 + y / x) = 2 + (x / y + y / x) := by 
    field_simp
    <;> ring
  have h6 : (1 + x / y) ^ 3 + (1 + y / x) ^ 3 = ((1 + x / y) + (1 + y / x)) ^ 3 - 3 * ((1 + x / y) * (1 + y / x)) * ((1 + x / y) + (1 + y / x)) := by 
    ring
  rw [h6, h4, h5]
  nlinarith [sq_nonneg ((x / y + y / x) - 2), sq_nonneg ((x / y + y / x) + 2), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy, h3]