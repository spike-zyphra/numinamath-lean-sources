import Mathlib

theorem algebra_10437 (A B C D E : ℝ × ℝ)
    (hA : A = (0, 5)) (hB : B = (1, 2)) (hC : C = (3, -4))
    (hD : D = (6, 0)) (hE : E = (-1, -2)) :
    max (max (max (max (Real.sqrt (A.1^2 + A.2^2)) (Real.sqrt (B.1^2 + B.2^2))) (Real.sqrt (C.1^2 + C.2^2))) (Real.sqrt (D.1^2 + D.2^2))) (Real.sqrt (E.1^2 + E.2^2)) = Real.sqrt (D.1^2 + D.2^2) := by
  rw [hA, hB, hC, hD, hE]
  have h1 : Real.sqrt ((0 : ℝ) ^ 2 + (5 : ℝ) ^ 2) = (5 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt ((1 : ℝ) ^ 2 + (2 : ℝ) ^ 2) = Real.sqrt (5 : ℝ) := by
    norm_num
  have h3 : Real.sqrt ((3 : ℝ) ^ 2 + (-4 : ℝ) ^ 2) = (5 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h4 : Real.sqrt ((6 : ℝ) ^ 2 + (0 : ℝ) ^ 2) = (6 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h5 : Real.sqrt ((-1 : ℝ) ^ 2 + (-2 : ℝ) ^ 2) = Real.sqrt (5 : ℝ) := by
    norm_num
  simp only [h1, h2, h3, h4, h5]
  have h5_le6 : Real.sqrt (5 : ℝ) ≤ (6 : ℝ) := by
    have h_nonneg : 0 ≤ (Real.sqrt (5 : ℝ) : ℝ) := Real.sqrt_nonneg 5
    have h_sq : (Real.sqrt (5 : ℝ)) ^ 2 ≤ (6 : ℝ) ^ 2 := by
      have h1' : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith
    nlinarith
  norm_num [max_eq_right, max_eq_left, h5_le6]