import Mathlib

theorem algebra_10141 (x y : ℝ) (hx : x > -1 / 2) (hy : y > -4) (hxy : 2 * x + y = 1) :
    1 / (2 * x + 1) + 9 / (y + 4) ≥ 8 / 3 := by 
  have h1 : 2 * x + 1 > 0 := by linarith 
  have h2 : y + 4 > 0 := by linarith
  have h3 : (2 * x + 1) + (y + 4) = 6 := by 
    linarith [hxy]
  have h4 : 1 / (2 * x + 1) + 9 / (y + 4) - 8 / 3 ≥ 0 := by
    have h5 : 0 < (2 * x + 1) * (y + 4) := by 
      apply mul_pos
      all_goals linarith
    have h6 : 3 * (y + 4) + 27 * (2 * x + 1) - 8 * (2 * x + 1) * (y + 4) ≥ 0 := by 
      nlinarith [sq_nonneg ((2 * x + 1) - 3 / 2), sq_nonneg ((y + 4) - 9 / 2), hxy, mul_pos (show 0 < 2 * x + 1 by linarith) (show 0 < y + 4 by linarith)]
    have h7 : (1 / (2 * x + 1) + 9 / (y + 4) - 8 / 3) = (3 * (y + 4) + 27 * (2 * x + 1) - 8 * (2 * x + 1) * (y + 4)) / (3 * (2 * x + 1) * (y + 4)) := by 
      field_simp
      <;> ring
    have h8 : (3 * (y + 4) + 27 * (2 * x + 1) - 8 * (2 * x + 1) * (y + 4)) / (3 * (2 * x + 1) * (y + 4)) ≥ 0 := by 
      apply div_nonneg
      linarith [h6]
      positivity
    linarith [h7, h8]
  linarith [h4]