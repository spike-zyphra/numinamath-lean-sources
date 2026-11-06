import Mathlib

theorem algebra_148952 (A B C : EuclideanSpace ℝ (Fin 3))
    (hA : A = ![ -1, -2, 1 ])
    (hB : B = ![ -4, -2, 5 ])
    (hC : C = ![ -8, -2, 2 ]) :
    let v1 := B - A
    let v2 := C - A
    let cosθ := (inner v1 v2) / (‖v1‖ * ‖v2‖)
    cosθ = 1 / Real.sqrt 2 := by
  subst_vars
  simp [Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_three]
  have h1 : ((-4 + 1 : ℝ) * (-8 + 1) + (5 - 1) * (2 - 1)) / (√((-4 + 1) ^ 2 + (5 - 1) ^ 2) * √((-8 + 1) ^ 2 + (2 - 1) ^ 2)) = 1 / Real.sqrt 2 := by
    have h2' : ((-4 + 1 : ℝ) * (-8 + 1) + (5 - 1) * (2 - 1)) = (25 : ℝ) := by
      norm_num 
    have h2 : √((-4 + 1 : ℝ) ^ 2 + (5 - 1 : ℝ) ^ 2) = (5 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt ((-8 + 1 : ℝ) ^ 2 + (2 - 1 : ℝ) ^ 2) = Real.sqrt 50 := by 
      norm_num 
    have h4 : ((-4 + 1 : ℝ) * (-8 + 1) + (5 - 1) * (2 - 1)) / (√((-4 + 1) ^ 2 + (5 - 1) ^ 2) * √((-8 + 1) ^ 2 + (2 - 1) ^ 2)) =
        (25 : ℝ) / (5 * Real.sqrt 50) := by
      rw [show √((-4 + 1) ^ 2 + (5 - 1) ^ 2) = (5 : ℝ) by exact h2, 
          show Real.sqrt ((-8 + 1 : ℝ) ^ 2 + (2 - 1 : ℝ) ^ 2) = Real.sqrt 50 by exact h3]
      all_goals linarith
    rw [h4]
    have h5 : Real.sqrt (50 : ℝ) = 5 * Real.sqrt 2 := by
      calc
        Real.sqrt (50 : ℝ) = Real.sqrt (5^2 * 2) := by norm_num
        _ = (Real.sqrt (5^2)) * (Real.sqrt (2 : ℝ)) := by rw [Real.sqrt_mul (by norm_num)]
        _ = (5 : ℝ) * (Real.sqrt (2 : ℝ)) := by rw [Real.sqrt_sq (by norm_num)]
    rw [h5]
    field_simp
    all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  norm_num at h1 ⊢
  all_goals linarith