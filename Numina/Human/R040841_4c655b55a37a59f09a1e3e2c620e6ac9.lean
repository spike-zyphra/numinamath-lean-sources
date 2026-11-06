import Mathlib

open Real Set

theorem algebra_239211 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + 2 * y = 4) :
    1 / x + 1 / y ≥ (3 + 2 * sqrt 2) / 4 := by

  have hx2 : x = 4 - 2 * y := by linarith
  rw [hx2]
  have h1 : 4 - 2 * y > 0 := by
    nlinarith [h, hx]
  have h3 : 1 / (4 - 2 * y) + 1 / y ≥ (3 + 2 * sqrt 2) / 4 := by
    have h4 : 0 < y := hy
    have h5 : y < 2 := by nlinarith [h, hx]
    have h6 : 4 - 2 * y > 0 := by nlinarith [h, hx]
    have h7 : (6 + 4 * sqrt 2) * (y - (4 - 2 * sqrt 2)) ^ 2 ≥ 0 := by
      apply mul_nonneg
      · have h71 : 6 + 4 * sqrt 2 > 0 := by
          linarith [show sqrt 2 > 0 by positivity]
        linarith
      · apply pow_two_nonneg
    have h8 : (6 + 4 * sqrt 2) * (y - (4 - 2 * sqrt 2)) ^ 2 = 6 * y^2 + 4 * sqrt 2 * y^2 - 16 * y - 8 * sqrt 2 * y + 16 := by
      ring_nf
      <;> simp [pow_two, mul_assoc, add_mul, sub_mul, mul_add, mul_sub]
      <;> ring
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h9 : 6 * y^2 + 4 * sqrt 2 * y^2 - 16 * y - 8 * sqrt 2 * y + 16 ≥ 0 := by
      linarith [h7, h8]
    have h10 : (1 / (4 - 2 * y) + 1 / y) - (3 + 2 * sqrt 2) / 4 ≥ 0 := by
      have h11 : 4 * y * (4 - 2 * y) * ((1 / (4 - 2 * y) + 1 / y) - (3 + 2 * sqrt 2) / 4) = 6 * y^2 + 4 * sqrt 2 * y^2 - 16 * y - 8 * sqrt 2 * y + 16 := by
        field_simp [h6, h4]
        ring_nf
        <;> simp [mul_assoc, add_mul, sub_mul, pow_two]
        <;> ring
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith [h9, mul_pos (mul_pos (show (0 : ℝ) < 4 by norm_num) h4) h6]
    linarith [h10]
  linarith [h3]