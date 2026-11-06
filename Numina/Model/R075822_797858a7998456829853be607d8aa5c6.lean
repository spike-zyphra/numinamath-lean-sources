import Mathlib

theorem inequalities_42799 (x y : ℝ) (hx : 1 < x) (hy : 1 < y) :
    8 ≤ x ^ 2 / (y - 1) + y ^ 2 / (x - 1) := by
  have pos1 : 0 < y - 1 := by linarith
  have pos2 : 0 < x - 1 := by linarith
  have h1 : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) - (8 : ℝ) ≥ 0 := by
    have pos3 : 0 < (y - 1) * (x - 1) := mul_pos pos1 pos2
    have h2 : x ^ 2 / (y - 1) + y ^ 2 / (x - 1) - (8 : ℝ) =
          (x^2 * (x - 1) + y^2 * (y - 1) - 8 * ((y - 1) * (x - 1))) / ((y - 1) * (x - 1)) := by 
        field_simp
        ring
    rw [h2]
    have h3 : x^2 * (x - 1) + y^2 * (y - 1) - 8 * ((y - 1) * (x - 1)) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2),
          mul_pos pos1 pos2]
    apply div_nonneg
    linarith
    all_goals linarith
  linarith