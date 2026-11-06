import Mathlib

theorem algebra_6049
    {A B C D : ℝ}
    (hAB : A / B = 3 / 2)
    (hBC : B / C = 7 / 5)
    (hCD : C / D = 2 / 5)
    (hA : A + B + C + D = 1470) :
    D - A = 84 := by

  have hB1 : B ≠ 0 := by
    by_contra h'
    rw [h'] at hAB
    norm_num at hAB
  
  have hC1 : C ≠ 0 := by
    by_contra h'
    rw [h'] at hBC
    norm_num at hBC
  
  have hD1 : D ≠ 0 := by
    by_contra h'
    rw [h'] at hCD
    norm_num at hCD
  
  have eq1 : 2 * A = 3 * B := by
    field_simp [hB1] at hAB
    linarith
  
  have eq2 : 5 * B = 7 * C := by
    field_simp [hC1] at hBC
    linarith
  
  have eq3 : 5 * C = 2 * D := by
    field_simp [hD1] at hCD
    linarith
  
  have h1 : C = 210 := by
    have h2 : B = 7 / 5 * C := by
      linarith [eq2]
    
    have h3 : A = 21 / 10 * C := by
      linarith [eq1, h2]
    
    have h4 : D = 5 / 2 * C := by
      linarith [eq3]
    
    linarith [hA, eq1, eq2, eq3, h2, h3, h4]

  have h2 : D = 525 := by 
    have h4 : D = 5 / 2 * C := by 
      linarith [eq3]
    
    rw [show C = 210 by linarith [h1]] at h4 
    linarith

  have h3 : A = 441 := by 
    have h4 : A = 21 / 10 * C := by 
      have h2 : B = 7 / 5 * C := by 
        linarith [eq2]
      linarith [eq1, h2]
    
    rw [show C = 210 by linarith [h1]] at h4 
    linarith
  
  linarith [h2, h3]