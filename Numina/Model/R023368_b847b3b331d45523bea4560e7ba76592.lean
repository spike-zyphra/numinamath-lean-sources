import Mathlib

open Real

theorem inequalities_104961 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x + y) / 2 ≥ sqrt (x * y) ∧ ((x + y) / 2 = sqrt (x * y) ↔ x = y) := by

  have h1 : (x + y) ^ 2 / 4 ≥ x * y := by
    nlinarith [sq_nonneg (x - y)]
  
  have h2 : (x + y) / 2 ≥ sqrt (x * y) := by
    have h3 : ((x + y) / 2) ^ 2 ≥ x * y := by
      nlinarith [sq_nonneg (x - y)]
    
    have h4 : ((x + y) / 2) ≥ 0 := by
      nlinarith
    have h5 : sqrt (x * y) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h6 : (sqrt (x * y)) ^ 2 = x * y := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [sq_nonneg ((x + y) / 2 - sqrt (x * y)), Real.sqrt_nonneg (x * y), show 0 ≤ (x + y) / 2 by linarith]
  
  have h_eq : (x + y) / 2 = sqrt (x * y) ↔ x = y := by 
    constructor
    · -- Assume (x + y) / 2 = sqrt (x * y) holds, prove x = y.
      intro heq
      have h_eq1 : ((x + y) / 2) ^ 2 = (sqrt (x * y)) ^ 2 := by 
        rw [heq]
    
      have h_eq2 : (sqrt (x * y)) ^ 2 = x * y := by
        rw [Real.sq_sqrt]
        nlinarith
      have h_eq3 : ((x + y) / 2) ^ 2 = x * y := by 
        linarith [h_eq1, h_eq2]
    
      have h_eq4 : (x - y) ^ 2 = 0 := by 
        nlinarith [h_eq3]
      have h_eq5 : x - y = 0 := by 
        nlinarith
      linarith
    · -- Assume x = y holds, prove (x + y) / 2 = sqrt (x * y).
      intro heq
      have h_eq1 : y = x := by 
        linarith [heq]
      rw [show y = x by linarith [heq]]
      have h_eq2 : sqrt (x * x) = x := by 
        have h_eq3 : sqrt (x * x) = x := by 
          have h_eq4 : x * x = x ^ 2 := by 
            nlinarith
          rw [h_eq4]
          have h_eq5 : sqrt (x ^ 2) = x := by 
            rw [Real.sqrt_sq]
            nlinarith
          exact h_eq5
        exact h_eq3
      linarith [h_eq2]
  
  constructor
  · exact h2
  · exact h_eq