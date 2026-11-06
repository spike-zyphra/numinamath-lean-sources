import Mathlib

theorem inequalities_315551 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    2 / (1 + x ^ 2) + 1 / (1 - y ^ 2) > 2 := by
  have h1 : y = 1 - x := by linarith 
  have h2 : 0 < y := by linarith [hxy, hx]
  have h3 : 0 < 1 - y^2 := by
    rw [h1]
    nlinarith [sq_pos_of_pos hx, sq_nonneg (1 - x)]
  have h4 : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have h5 : 1 - y ^ 2 = 2*x - x^2 := by 
    rw [h1]
    nlinarith [hxy]
  have h6 : 2 / (1 + x ^ 2) + 1 / (1 - y ^ 2) - 2 > 0 := by 
    rw [h5]
    have h6a : (1 + x ^ 2) > 0 := by nlinarith [sq_nonneg x]
    have h6b : (2 * x - x ^ 2) > 0 := by 
      nlinarith [show x > 0 by linarith, show x < 1 by nlinarith [hxy, hx, hy], sq_pos_of_pos hx]
    have h6c : (2 / (1 + x ^ 2) + 1 / (2 * x - x ^ 2) - 2) =
      (2 * (2 * x - x ^ 2) + (1 + x ^ 2) - 2 * (1 + x ^ 2) * (2 * x - x ^ 2)) 
      / ((1 + x ^ 2) * (2 * x - x ^ 2)) := by 
      field_simp [(show (1 + x ^ 2) ≠ 0 by nlinarith [sq_nonneg x]), 
                  (show (2 * x - x ^ 2) ≠ 0 by 
                      nlinarith [show x > 0 by linarith, show x < 1 by nlinarith [hxy, hx, hy]])]
      <;> ring 
    have h6d : 2 * (2 * x - x ^ 2) + (1 + x ^ 2) - 2 * (1 + x ^ 2) * (2 * x - x ^ 2) > 0 := by 
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x), mul_pos hx (show 0 < y from by linarith), 
                hxy, sq_pos_of_pos hx, sq_pos_of_pos (show 0 < y from by linarith)]
    have h6e : (1 + x ^ 2) * (2 * x - x ^ 2) > 0 := by 
      positivity 
    rw [h6c]
    apply div_pos 
    linarith 
    all_goals positivity 
  linarith [h6]