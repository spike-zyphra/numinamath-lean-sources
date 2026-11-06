import Mathlib

open Real Set

theorem algebra_320864 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    ((x + 1) / x)^2 + ((y + 1) / y)^2 ≥ 25 / 2 := by
  have h1 : y = 1 - x := by linarith
  rw [h1]
  have h2 : x < 1 := by
    nlinarith
  have hx3 : x ≠ 0 := by linarith
  have hx4 : (1 - x) ≠ 0 := by
    intro h
    nlinarith
  have eq1 : ((x + 1) / x) ^ 2 + ((1 - x + 1) / (1 - x)) ^ 2 ≥ 25 / 2 := by
    have h5 : ((x + 1) / x) ^ 2 + ((1 - x + 1) / (1 - x)) ^ 2 - 25 / 2 ≥ 0 := by
      have hx3 : x ≠ 0 := by linarith
      have hx4 : (1 - x) ≠ 0 := by
        intro h
        nlinarith
      have h7 : x * (1 - x) > 0 := by
        apply mul_pos
        all_goals linarith
      have h8 : ((x + 1) / x) ^ 2 + ((1 - x + 1) / (1 - x)) ^ 2 - 25 / 2 =
          (2 * (x + 1) ^ 2 * (1 - x) ^ 2 + 2 * (2 - x) ^ 2 * x ^ 2 - 25 * x ^ 2 * (1 - x) ^ 2) / (2 * x ^ 2 * (1 - x) ^ 2) := by
        field_simp [(show x ≠ 0 by linarith), (show (1 - x) ≠ 0 by
          intro h
          nlinarith
        )]
        ring
      rw [h8] at *
      apply div_nonneg
      nlinarith [sq_nonneg (x - 2 / 5), sq_nonneg (x - 1 / 2), sq_nonneg (x - 3 / 5), 
        sq_nonneg ((1 - x) - 2 / 5), sq_nonneg (x * (1 - x) - 1 / 25 * 9), 
        sq_nonneg ((x - (1 - x))), mul_pos hx (show 0 < (1 - x) by nlinarith), 
        sq_nonneg (x ^ 2 - (1 - x) ^ 2), sq_nonneg (x * (1 - x) - 1 / 4)]
      positivity
    linarith
  linarith