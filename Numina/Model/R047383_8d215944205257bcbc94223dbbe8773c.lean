import Mathlib

theorem algebra_148721 (A B C : EuclideanSpace ℝ (Fin 3))
    (hA : A = ![ -3, -7, -5 ])
    (hB : B = ![ 0, -1, -2 ])
    (hC : C = ![ 2, 3, 0 ]) :
    let v1 := B - A
    let v2 := C - A
    let cosθ := (inner v1 v2) / (norm v1 * norm v2)
    cosθ = 1 := by
  subst_vars
  simp [Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.sum_univ_three, inner, EuclideanSpace.norm_eq, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h : Real.sqrt 54 * Real.sqrt 150 = (90 : ℝ) := by
    have h2 : Real.sqrt 54 * Real.sqrt 150 = Real.sqrt (54 * 150 : ℝ) := by 
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h2]
    rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
  norm_num [h]
  all_goals norm_num