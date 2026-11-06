import Mathlib

theorem algebra_305895 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) :
    1 / x ^ 4 + 1 / (4 * y ^ 4) ≥ 1 := by

  have h1 : y > 0 := by
    nlinarith [hxy, hx, hy]
  have h2 : x > 0 := hx

  have h3 : x * y = 1 := hxy
  have h4 : y = 1 / x := by
    field_simp [show x ≠ 0 by linarith]
    nlinarith
  
  have h5 : 1 / x ^ 4 + 1 / (4 * y ^ 4) = 1 / x ^ 4 + (x ^ 4) / 4 := by
    rw [h4]
    field_simp [show x ≠ 0 by linarith]
    <;> ring

  rw [h5]

  have hx4_pos : x ^ 4 > 0 := by positivity

  suffices (1 / x ^ 4 + (x ^ 4) / 4 - 1) ≥ 0 by linarith

  have h6 : (1 / x ^ 4 + (x ^ 4) / 4 - 1) = ((x ^ 4 - 2) ^ 2) / (4 * x ^ 4) := by
    field_simp [hx4_pos]
    ring

  rw [h6]
  
  have h7 : ((x ^ 4 - 2) ^ 2) / (4 * x ^ 4) ≥ 0 := by
    apply div_nonneg
    · apply pow_two_nonneg
    · positivity
  
  linarith