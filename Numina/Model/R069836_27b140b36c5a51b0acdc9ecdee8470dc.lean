import Mathlib

theorem algebra_119159 (x y z : ℝ) (hx : x ≥ 2) (hy : y ≥ 8) (hz : z ≥ 4)
    (h : x + y + z = 2 * Real.sqrt (x - 2) + 2 * Real.sqrt (y - 8) + 10 * Real.sqrt (z - 4) - 13) :
    x = 3 ∧ y = 9 ∧ z = 29 := by 
  have h1 : Real.sqrt (x - 2) ≥ 0 := Real.sqrt_nonneg (x - 2)
  have h2 : Real.sqrt (y - 8) ≥ 0 := Real.sqrt_nonneg (y - 8)
  have h3 : Real.sqrt (z - 4) ≥ 0 := Real.sqrt_nonneg (z - 4)
  have h_eq1 : (Real.sqrt (x - 2) - 1) ^ 2 + (Real.sqrt (y - 8) - 1) ^ 2 + (Real.sqrt (z - 4) - 5) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (Real.sqrt (y - 8) - 1), sq_nonneg (Real.sqrt (z - 4) - 5),
      Real.sq_sqrt (show (x - 2 : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (y - 8 : ℝ) ≥ 0 by linarith), Real.sq_sqrt (show (z - 4 : ℝ) ≥ 0 by linarith)]
  have h_eq2 : Real.sqrt (x - 2) - 1 = 0 := by 
    nlinarith [sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (Real.sqrt (y - 8) - 1), sq_nonneg (Real.sqrt (z - 4) - 5),
      h_eq1
    ]
  have h_eq3 : Real.sqrt (y - 8) - 1 = 0 := by 
    nlinarith [sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (Real.sqrt (y - 8) - 1), sq_nonneg (Real.sqrt (z - 4) - 5),
      h_eq1
    ]
  have h_eq4 : Real.sqrt (z - 4) - 5 = 0 := by 
    nlinarith [sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (Real.sqrt (y - 8) - 1), sq_nonneg (Real.sqrt (z - 4) - 5),
      h_eq1
    ]
  have h_eq5 : Real.sqrt (x - 2) = 1 := by linarith [h_eq2]
  have h_eq6 : Real.sqrt (y - 8) = 1 := by linarith [h_eq3]
  have h_eq7 : Real.sqrt (z - 4) = 5 := by linarith [h_eq4]
  have h_eq8 : x - 2 = 1 := by 
    calc
      x - 2 = (Real.sqrt (x - 2)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith
      _ = 1 ^ 2 := by rw [h_eq5]
      _ = (1 : ℝ) := by norm_num
  have h_eq9 : y - 8 = 1 := by 
    calc
      y - 8 = (Real.sqrt (y - 8)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith
      _ = 1 ^ 2 := by rw [h_eq6]
      _ = (1 : ℝ) := by norm_num
  have h_eq10 : z - 4 = 25 := by 
    calc
      z - 4 = (Real.sqrt (z - 4)) ^ 2 := by 
        rw [Real.sq_sqrt]
        linarith
      _ = 5 ^ 2 := by rw [h_eq7]
      _ = (25 : ℝ) := by norm_num
  have hx_eq : x = 3 := by 
    linarith [h_eq8]
  have hy_eq : y = 9 := by 
    linarith [h_eq9]
  have hz_eq : z = 29 := by 
    linarith [h_eq10]
  exact ⟨hx_eq, hy_eq, hz_eq⟩