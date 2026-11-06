import Mathlib

theorem inequalities_602632 {x y : ℝ} (hy : 0 ≤ y) (hxy : y < x) :
    3 ≤ x + 4 / ((x - y) * (y + 1)^2) := by
  have hx1 : 0 < x - y := by linarith
  have hx2 : 0 < (x - y) * (y + 1)^2 := by
    positivity

  have h1 : x + 4 / ((x - y) * (y + 1)^2) - 3 ≥ 0 := by
    have h2 : 0 < (x - y) * (y + 1)^2 := hx2
    have h3 : x + 4 / ((x - y) * (y + 1)^2) - 3 = ((x - 3) * ((x - y) * (y + 1)^2) + 4) / ((x - y) * (y + 1)^2) := by
      field_simp
      <;> ring
    rw [h3] 
    apply div_nonneg
    -- Prove the numerator is non-negative
    have h4 : ((x - 3) * ((x - y) * (y + 1)^2) + 4) ≥ 0 := by
      nlinarith [sq_nonneg ((x - y) - 1), sq_nonneg (y - 1), sq_nonneg (x - y - 2), sq_nonneg (x + y - 2), 
          sq_nonneg ((y + 1)^2 -1), sq_nonneg ((x - y) * (y +1) - 2), 
          mul_pos (sub_pos.mpr hxy) (show 0 < (y + 1) by nlinarith), 
          sq_nonneg (x - 3 + y), sq_nonneg (x - y -1), 
          mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ y + 1 by nlinarith), 
          mul_pos (sub_pos.mpr hxy) (show 0 < y + 1 by nlinarith), 
          sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x - 2 * y), 
          sq_nonneg (x - y - (y)), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ x - y by linarith) 
        ]
    all_goals
      nlinarith
    all_goals positivity

  linarith