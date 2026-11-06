import Mathlib

theorem algebra_99209 (x y z : ℚ) (hx : x ≠ -1) (hy : y ≠ -2) (hz : z ≠ -3)
    (h : 2015 / (x + 1) + 2015 / (y + 2) + 2015 / (z + 3) = 2014) :
    (x - 1) / (x + 1) + y / (y + 2) + (z + 1) / (z + 3) = 2017 / 2015 := by
  have h1 : x + 1 ≠ 0 := by 
    intro h2
    apply hx
    linarith
  have h2 : y + 2 ≠ 0 := by 
    intro h3
    apply hy
    linarith
  have h3 : z + 3 ≠ 0 := by 
    intro h4
    apply hz
    linarith
  
  have eq2 : 1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3) = 2014 / 2015 := by
    have h4 : x + 1 ≠ 0 := h1
    have h5 : y + 2 ≠ 0 := h2
    have h6 : z + 3 ≠ 0 := h3
    have eq3 : 2015 / (x + 1) + 2015 / (y + 2) + 2015 / (z + 3) = 2014 := by 
      linarith [h]
    
    have eq4 : 2015 / (x + 1) + 2015 / (y + 2) + 2015 / (z + 3) = 2015 * (1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3)) := by
      field_simp [h4, h5, h6] at *
      <;> ring
      all_goals norm_num at *
      all_goals nlinarith
      all_goals ring
      all_goals field_simp [h4, h5, h6] at *
      all_goals nlinarith
      all_goals ring_nf
      all_goals field_simp [h4, h5, h6] at *
      all_goals nlinarith

    rw [eq4] at eq3

    have eq5 : 1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3) = 2014 / 2015 := by
      have h7 : (2015 : ℚ) * (1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3)) = 2014 := by 
        linarith [eq3]
      have eq6 : 1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3) = 2014 / 2015 := by 
        field_simp at h7 ⊢
        <;> nlinarith
        all_goals nlinarith
        all_goals field_simp at h7 ⊢
        all_goals nlinarith
      linarith [eq6]
    
    linarith [eq5]
  
  have eq_1 : (x - 1) / (x + 1) = 1 - 2 / (x + 1) := by 
    field_simp [(show (x + 1 : ℚ) ≠ 0 by assumption)]
    <;> ring
    all_goals field_simp [(show (x + 1 : ℚ) ≠ 0 by assumption)]
    all_goals ring
  
  have eq_3 : (z + 1) / (z + 3) = 1 - 2 / (z + 3) := by 
    field_simp [(show (z + 3 : ℚ) ≠ 0 by assumption)]
    <;> ring
    all_goals field_simp [(show (z + 3 : ℚ) ≠ 0 by assumption)]
    all_goals ring
  
  have eq3 : (x - 1) / (x + 1) + y / (y + 2) + (z + 1) / (z + 3) = (1 - 2 / (x + 1) ) + y / (y + 2) + (1 - 2 / (z + 3)) := by 
    rw [eq_1, eq_3]
    all_goals ring
    all_goals field_simp [(show (x + 1 : ℚ) ≠ 0 by assumption), (show (z + 3 : ℚ) ≠ 0 by assumption)]
    all_goals ring
  
  rw [eq3]
  
  have h_eq2 : 1 / (x + 1) + 1 / (z + 3) = (2014 / 2015 : ℚ) - 1 / (y + 2) := by
    have eq_1 : 1 / (x + 1) + 1 / (y + 2) + 1 / (z + 3) = 2014 / 2015 := by
      assumption
    linarith
  
  have eq3 : (1 - 2 / (x + 1) ) + y / (y + 2) + (1 - 2 / (z + 3)) = 2017 / 2015 := by 
    have h_eq3 : (1 - 2 / (x + 1) ) + y / (y + 2) + (1 - 2 / (z + 3)) =
        2 + y / (y + 2) - 2 * ( (1 / (x + 1) ) + (1 / (z + 3) ) ) := by 
      field_simp [(show (x + 1 : ℚ) ≠ 0 by assumption), 
      (show (z + 3 : ℚ) ≠ 0 by assumption)]
      <;> ring
      all_goals field_simp [(show (x + 1 : ℚ) ≠ 0 by assumption), 
      (show (z + 3 : ℚ) ≠ 0 by assumption)]
      all_goals ring
      all_goals field_simp [(show (x + 1 : ℚ) ≠ 0 by assumption), 
      (show (z + 3 : ℚ) ≠ 0 by assumption)]
      all_goals ring

    rw [h_eq3]

    rw [h_eq2]

    have h_eq4 : (2 + y / (y + 2) - 2 * ((2014 / 2015 : ℚ) - 1 / (y + 2))) = 2017 / 2015 := by 
      have h_eq5 : y + 2 ≠ 0 := h2
      field_simp [h_eq5]
      linarith 
      all_goals field_simp [h_eq5]
      all_goals nlinarith
      all_goals ring_nf
      all_goals field_simp [h_eq5]
      all_goals nlinarith

    linarith [h_eq4]
  
  linarith [eq3]
  all_goals linarith
  all_goals assumption
  all_goals nlinarith
  all_goals field_simp [(show (x + 1 : ℚ) ≠ 0 by assumption), (show (y + 2 : ℚ) ≠ 0 by assumption), (show (z + 3 : ℚ) ≠ 0 by assumption)]
  all_goals nlinarith