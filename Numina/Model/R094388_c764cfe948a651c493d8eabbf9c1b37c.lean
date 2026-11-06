import Mathlib

theorem algebra_15752 {P : ℝ × ℝ} (hP : P.1 > 0 ∧ P.2 > 0) (hP1 : P.2 = P.1 ^ 2 / 4)
    (hP2 : Real.sqrt ((P.1 ^ 2 + (P.2 - 1) ^ 2)) = 101) :
    P = (20, 100) := by
  have h1 : P.1 ^ 2 + (P.2 - 1) ^ 2 = (101 : ℝ) ^ 2 := by
    calc
      P.1 ^ 2 + (P.2 - 1) ^ 2 = (Real.sqrt ((P.1 ^ 2 + (P.2 - 1) ^ 2))) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
      _ = (101 : ℝ) ^ 2 := by
        rw [hP2]
  
  have eq1 : P.1 ^ 2 + (P.2 - 1) ^ 2 = (101 : ℝ) ^ 2 := h1
  
  rw [hP1] at eq1

  have h_eq : P.1^2 + (P.1^2 / 4 - 1)^2 = (101 : ℝ) ^ 2 := by
    linarith
  
  have h_eq2 : P.1^4 + 8 * P.1^2 - 163200 = 0 := by
    nlinarith
  
  have h3 : P.1^2 - 400 = 0 := by
    nlinarith [sq_nonneg (P.1^2 - 400), sq_nonneg (P.1^2 + 400)]
  
  have h4 : P.1^2 = 400 := by 
    linarith
  
  have h5 : P.1 = 20 := by 
    nlinarith [sq_nonneg (P.1 - 20), sq_nonneg (P.1 + 20), hP.1]
  
  have h6 : P.2 = 100 := by 
    rw [hP1]
    nlinarith
  
  exact Prod.ext h5 h6