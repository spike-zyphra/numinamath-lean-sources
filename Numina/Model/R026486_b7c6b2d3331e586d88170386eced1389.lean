import Mathlib

open Real Set

theorem algebra_321385 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) :
    x ^ 2 / (x + 2) + y ^ 2 / (y + 1) ≥ 1 / 4 := by

  have h1 : y = 1 - x := by linarith
  rw [h1]
  have h2 : x + 2 > 0 := by linarith
  have h3 : (1 - x : ℝ) + 1 > 0 := by
    have h4 : x < 1 := by nlinarith [show 0 < (1 - x : ℝ) by nlinarith]
    nlinarith
  have h4 : (2 - x : ℝ) > 0 := by
    have h5 : x < 1 := by nlinarith [show 0 < (1 - x : ℝ) by nlinarith]
    nlinarith
  have h5 : x ^ 2 / (x + 2) + ( (1 - x : ℝ) ) ^ 2 / ( (1 - x + 1 : ℝ) ) ≥ 1 / 4 := by

    have pos1 : (x + 2 : ℝ) > 0 := by linarith
    have pos2 : ( (1 - x + 1 : ℝ ) ) > 0 := by
      have h6 : x < 1 := by nlinarith [show 0 < (1 - x : ℝ ) by nlinarith]
      nlinarith
    have h6 : x ^ 2 / (x + 2) + ( (1 - x : ℝ ) ) ^ 2 / ( (1 - x + 1 : ℝ ) ) - (1 / 4 : ℝ ) ≥ 0 := by
      have h7 : x ^ 2 / (x + 2) + ( (1 - x : ℝ ) ) ^ 2 / ( (1 - x + 1 : ℝ ) ) - (1 / 4 : ℝ ) =
          (4 * x^2 * (2 - x) + 4 * ( (1 - x )^2 ) * (x + 2) - (x + 2 ) * (2 - x ) ) / (4 * (x + 2 ) * (2 - x ) ) := by
        field_simp
        ring
      rw [h7] at *
      apply div_nonneg
      nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (x - 1 / 3), sq_nonneg (x * (x - 2 / 3) ) ]
      positivity
    linarith
  linarith