import Mathlib

theorem algebra_141387 (A B C : EuclideanSpace ℝ (Fin 3))
    (hA : A = ![x, 0, 0]) (hB : B = ![4, 5, -2]) (hC : C = ![2, 3, 4])
    (hAB : dist A B = dist A C) :
    A = ![4, 0, 0] := by
  rw [hA] at hAB
  rw [hB] at hAB
  rw [hC] at hAB
  simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_sq] at hAB
  have h2 : (4 - x) ^ 2 + (29 : ℝ) = (2 - x) ^ 2 + (25 : ℝ) := by
    have h3 : Real.sqrt ((4 - x) ^ 2 + (29 : ℝ)) = Real.sqrt ((2 - x) ^ 2 + (25 : ℝ)) := by
      ring_nf at hAB ⊢
      linarith
    have h4 : (Real.sqrt ((4 - x) ^ 2 + (29 : ℝ))) ^ 2 = (Real.sqrt ((2 - x) ^ 2 + (25 : ℝ))) ^ 2 := by
      rw [h3]
    rw [Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)] at h4
    linarith
  have hx : x = 4 := by
    nlinarith
  rw [hx] at hA
  simpa using hA