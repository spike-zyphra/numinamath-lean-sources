import Mathlib

theorem inequalities_321571 (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) :
    2 / (1 - x * y) ≤ 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) := by 
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : -1 < y := by linarith [abs_lt.mp hy]
  have h4 : y < 1 := by linarith [abs_lt.mp hy]
  have h1' : 1 - x^2 > 0 := by
    nlinarith
  have h2' : 1 - y^2 > 0 := by
    nlinarith 
  have h3' : 1 - x * y > 0 := by 
    nlinarith [abs_lt.mp hx, abs_lt.mp hy, sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - x), sq_nonneg (x * y), mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h3) (sub_pos.mpr h4)]
  have h4' : 1 - x ^ 2 > 0 := h1'
  have h5' : 1 - y ^ 2 > 0 := h2'
  have h7 : 1 / (1 - x^2) + 1 / (1 - y^2) - 2 / (1 - x * y) ≥ 0 := by 
    have h7a : (1 - x^2) * (1 - y^2) * (1 - x * y) > 0 := by positivity 
    have h7b : (1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y)) = ((1 - y^2) * (1 - x * y) + (1 - x^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2)) / ((1 - x^2) * (1 - y^2) * (1 - x * y)) := by
      field_simp [(show 1 - x ^ 2 ≠ 0 by nlinarith), (show 1 - y^2 ≠ 0 by nlinarith), (show 1 - x * y ≠ 0 by nlinarith)]
      <;> ring
    rw [h7b] 
    apply div_nonneg
    · -- Show that the numerator is non-negative 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - (x * y)), sq_nonneg (x * y), sq_nonneg (x - (-y)), sq_nonneg (x * y - 1)]
    all_goals 
      positivity 
  linarith [h7]