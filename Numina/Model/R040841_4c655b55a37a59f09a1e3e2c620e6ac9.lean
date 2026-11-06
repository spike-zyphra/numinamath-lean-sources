import Mathlib

open Real Set

theorem algebra_239211 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x + 2 * y = 4) :
    1 / x + 1 / y ≥ (3 + 2 * sqrt 2) / 4 := by
  have h1 : x = 4 - 2 * y := by linarith
  rw [h1]
  have h2 : (4 - 2 * y) > 0 := by
    nlinarith [show x > 0 by linarith, h]
  have h3 : y > 0 := by linarith [hy]

  have h4 : 0 < 4 - 2 * y := by nlinarith
  have h5 : y * (4 - 2 * y) > 0 := by nlinarith [show y > 0 by linarith, show 4 - 2 * y > 0 by nlinarith]

  have h7 : (1 / (4 - 2 * y) + 1 / y) ≥ (3 + 2 * sqrt 2) / 4 := by
    have h8 : (1 / (4 - 2 * y) + 1 / y) - ( (3 + 2 * sqrt 2) / 4 ) ≥ 0 := by
      have h9 : 0 < y := by linarith
      have h10 : 0 < 4 - 2 * y := by nlinarith
      have h11 : (y) * (4 - 2 * y) > 0 := by nlinarith
      have h12 : (1 / (4 - 2 * y) + 1 / y) - ( (3 + 2 * sqrt 2) / 4 ) =
          ( (4 - y) / (y * (4 - 2 * y)) - ( (3 + 2 * sqrt 2) / 4 ) ) := by 
        field_simp [h9, h10]
        <;> ring 
      rw [h12]
      have h13 : ( (4 - y) / (y * (4 - 2 * y)) - ( (3 + 2 * sqrt 2) / 4 ) ) =
          ( 4 * (4 - y) - (3 + 2 * sqrt 2) * (y * (4 - 2 * y)) ) / ( 4 * (y * (4 - 2 * y)) ) := by
        field_simp
        <;> ring
      rw [h13]
      have h14 : 4 * (4 - y) - (3 + 2 * sqrt 2) * (y * (4 - 2 * y)) ≥ 0 := by
        nlinarith [ sq_nonneg (y - (4 - 2 * sqrt 2) ), sq_nonneg ( (4 - 2 * y) - ( -4 + 4 * sqrt 2) ), 
            Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), 
            sq_nonneg (y - (4 - 2 * sqrt 2) ), sq_nonneg ( (4 - 2 * y) + (4 * sqrt 2 -4) ), 
            mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < (4 - 2 * y) by nlinarith), 
            sq_nonneg (y * (4 - 2 * y) - (4 - 2 * sqrt 2) * ( 4 * sqrt 2 - 4) ) ]
      have h15 : 4 * (y * (4 - 2 * y) ) > 0 := by 
        nlinarith
      apply div_nonneg 
      · nlinarith 
      · nlinarith 
    linarith

  linarith