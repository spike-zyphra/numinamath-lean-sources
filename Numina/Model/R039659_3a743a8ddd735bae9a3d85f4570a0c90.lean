import Mathlib

theorem algebra_597033 : 10 / Real.tan (Real.arctan (1 / 3) + Real.arctan (1 / 7) + Real.arctan (1 / 13) + Real.arctan (1 / 21)) = 15 := by

  have h1 : Real.arctan (1/3) + Real.arctan (1/7) + Real.arctan (1/13) + Real.arctan (1/21) = Real.arctan (2/3) := by
    have h2 : Real.arctan (1/3) + Real.arctan (1/7) = Real.arctan (1/2) := by 
      rw [Real.arctan_add]
      norm_num
      all_goals norm_num
    have h3 : Real.arctan (1/13) + Real.arctan (1/21) = Real.arctan (1/8) := by 
      rw [Real.arctan_add]
      norm_num
      all_goals norm_num
    have h4 : Real.arctan (1/2) + Real.arctan (1/8) = Real.arctan (2/3) := by 
      rw [Real.arctan_add]
      norm_num
      all_goals norm_num 
    have eq1 : Real.arctan (1/3) + Real.arctan (1/7) + Real.arctan (1/13) + Real.arctan (1/21) = (Real.arctan (1/3) + Real.arctan (1/7)) + (Real.arctan (1/13) + Real.arctan (1/21)) := by ring 
    rw [eq1]
    rw [h2, h3]
    exact h4

  have h2 : Real.tan (Real.arctan (1 / 3) + Real.arctan (1 / 7) + Real.arctan (1 / 13) + Real.arctan (1 / 21)) = 2/3 := by 
    rw [h1]
    rw [Real.tan_arctan]

  have h3 : (10 / (Real.tan (Real.arctan (1 / 3) + Real.arctan (1 / 7) + Real.arctan (1 / 13) + Real.arctan (1 / 21)) ) ) = 15 := by 
    rw [h2]
    norm_num 

  exact h3