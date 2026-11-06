import Mathlib

theorem algebra_16408 {P Q R S T : EuclideanSpace ℝ (Fin 2)}
    (hP : P = ![0, 6]) (hQ : Q = ![3, 6]) (hR : R = ![3, 3])
    (hT : T = ![0, 0]) (hS : S = ![7, 0]) :
    dist P Q + dist Q R + dist R S + dist S T + dist T P = 24 := by
  rw [hP, hQ, hR, hS, hT]
  simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_succ, Fin.sum_univ_zero]
  ring_nf
  have h1 : Real.sqrt (9 : ℝ) = 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt (25 : ℝ) = 5 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : Real.sqrt (36 : ℝ) = 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h4 : Real.sqrt (49 : ℝ) = 7 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  simp [h1, h2, h3, h4]
  all_goals norm_num