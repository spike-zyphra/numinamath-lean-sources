import Mathlib

theorem algebra_144430 (A B C : EuclideanSpace ℝ (Fin 3)) (hA : A = ![0, y, 0]) (hB : B = ![7, 3, -4])
    (hC : C = ![1, 5, 7]) (hAB : dist A B = dist A C) :
    y = 1 / 4 := by
  rw [dist_eq_norm, dist_eq_norm] at hAB
  rw [hA, hB, hC] at hAB
  simp [norm_eq_sqrt_real_inner, Fin.sum_univ_three, inner, Fin.sum_univ_succ, Fin.sum_univ_zero] at hAB
  have eq1 : (65 + (y - 3) ^ 2 : ℝ) = (50 + (y - 5) ^ 2 : ℝ) := by
    have h2 : Real.sqrt (65 + (y - 3) ^ 2 : ℝ) = Real.sqrt (50 + (y - 5) ^ 2 : ℝ) := by
      ring_nf at hAB ⊢
      all_goals nlinarith
    have h3 : (Real.sqrt (65 + (y - 3) ^ 2 : ℝ)) ^ 2 = (Real.sqrt (50 + (y - 5) ^ 2 : ℝ)) ^ 2 := by
      rw [h2]
    have h4 : (Real.sqrt (65 + (y - 3) ^ 2 : ℝ)) ^ 2 = 65 + (y - 3) ^ 2 := Real.sq_sqrt (by positivity)
    have h5 : (Real.sqrt (50 + (y - 5) ^ 2 : ℝ)) ^ 2 = 50 + (y - 5) ^ 2 := Real.sq_sqrt (by positivity)
    linarith [h3, h4, h5]
  nlinarith