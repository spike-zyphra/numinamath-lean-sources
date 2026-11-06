import Mathlib

theorem algebra_236638 {x y z : ℝ} (h1 : y * z = 3 * y + 2 * z - 8) (h2 : z * x = 4 * z + 3 * x - 8)
    (h3 : x * y = 2 * x + y - 1) :
    (x = 2 ∧ y = 3 ∧ z = 1) ∨ (x = 3 ∧ y = 5 / 2 ∧ z = -1) := by

  have eq1 : (y - 2) * (z - 3) = -2 := by 
    nlinarith
  
  have eq2 : (z - 3) * (x - 4) = 4 := by
    nlinarith
  
  have eq3 : (x - 1) * (y - 2) = 1 := by 
    nlinarith
  
  have eq4 : z^2 = 1 := by 
    nlinarith [sq_nonneg (z - 3), sq_nonneg (x - 4), sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (z - 3), sq_nonneg (x - 4)]
  
  have h4 : z = 1 ∨ z = -1 := by 
    have h5 : z^2 = 1 := eq4
    rw [sq_eq_one_iff] at h5
    tauto
  
  cases h4 with
  | inl h5z1 =>
    
    have eq5y3 : y = 3 := by 
      have eq6 : (y - 2) * (z - 3) = -2 := eq1
      rw [show z - 3 = (1 : ℝ) - 3 by linarith [h5z1]] at eq6
      have eq7 : (y - 2) * (-2) = -2 := by
        linarith
      have eq8 : y - 2 = 1 := by
        linarith
      linarith
  
    have eq6x2 : x = 2 := by 
      have eq7 : (x - 1) * (y - 2) = 1 := eq3
      rw [show y - 2 = 1 by linarith [eq5y3] ] at eq7 
      have eq8 : (x - 1) * 1 = 1 := by
        linarith
      have eq9 : x - 1 = 1 := by
        linarith
      linarith
  
    left
    constructor
    · exact_mod_cast eq6x2
    constructor
    · exact_mod_cast eq5y3
    · exact_mod_cast h5z1
  
  | inr h5z1 =>
    
    have eq5y52 : y = 5/2 := by
      have eq6 : (y - 2) * (z - 3) = -2 := eq1
      rw [show z - 3 = (-1 : ℝ) - 3 by linarith [h5z1] ] at eq6
      have eq7 : (y - 2) * (-4) = -2 := by
        linarith
      have eq8 : y - 2 = 1/2 := by
        linarith
      linarith
  
    have eq6x3 : x = 3 := by 
      have eq7 : (x - 1) * (y - 2) = 1 := eq3
      rw [show y - 2 = (1/2 : ℝ) by linarith [eq5y52] ] at eq7 
      have eq8 : (x - 1) * (1/2) = 1 := by 
        linarith 
      have eq9 : x - 1 = 2 := by
        linarith
      linarith
  
    right
    constructor
    · exact_mod_cast eq6x3
    constructor
    · exact_mod_cast eq5y52
    · exact_mod_cast h5z1