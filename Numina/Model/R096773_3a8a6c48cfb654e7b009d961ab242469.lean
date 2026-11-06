import Mathlib

theorem inequalities_261760 (x y : ℝ) (hx : abs x < 1) (hy : abs y < 1) :
    1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) ≥ 2 / (1 - x * y) := by

  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : -1 < y := by linarith [abs_lt.mp hy]
  have h4 : y < 1 := by linarith [abs_lt.mp hy]

  have h5 : 1 - x^2 > 0 := by nlinarith
  have h6 : 1 - y^2 > 0 := by nlinarith
  have h7 : 1 - x * y > 0 := by nlinarith [mul_pos (show 0 < (1 - x) by nlinarith) (show 0 < (1 - y) by nlinarith), mul_pos (show 0 < (1 + x) by nlinarith) (show 0 < (1 + y) by nlinarith)]

  have h8 : 0 < 1 - x ^ 2 := by linarith
  have h9 : 0 < 1 - y ^ 2 := by linarith
  have h10 : 0 < 1 - x * y := by nlinarith

  have h11 : (1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y)) ≥ 0 := by
    have h12 : 0 < (1 - x^2) * (1 - y^2) * (1 - x * y) := by positivity
    have h13 : (1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y)) =
      ((1 - y^2) * (1 - x * y) + (1 - x^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2)) / ((1 - x^2) * (1 - y^2) * (1 - x * y)) := by
      field_simp [h8, h9, h10]
      <;> ring_nf <;> nlinarith
    rw [h13]
    apply div_nonneg 
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - 1 / 2), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x * y - 1)]
    all_goals positivity

  linarith