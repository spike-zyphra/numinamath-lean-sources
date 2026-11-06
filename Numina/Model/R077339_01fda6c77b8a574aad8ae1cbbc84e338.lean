import Mathlib

theorem algebra_259772 {a b c : ℝ} (ha : a ≠ 0) (h1 : a * (-1)^2 + b * (-1) + c = 2)
    (h2 : a * (-2)^2 + b * (-2) + c = 1) (h3 : a * 1^2 + b * 1 + c = 61) :
    a = 19 / 2 ∧ b = 59 / 2 ∧ c = 44 / 2 := by 
  have eq1 : a - b + c = 2 := by 
    linarith
  
  have eq2 : 4 * a - 2 * b + c = 1 := by 
    linarith
  
  have eq3 : a + b + c = 61 := by
    linarith
  
  have hb : b = 59 / 2 := by 
    linarith [eq1, eq3]

  have ha' : a = 19 / 2 := by
    have eq4 : a + c = 63 / 2 := by
      linarith [eq1, hb]
    
    have eq5 : 4 * a + c = 60 := by 
      linarith [eq2, hb]
    
    linarith [eq4, eq5]

  have hc : c = 44 / 2 := by
    linarith [eq3, hb, ha']
  
  exact ⟨ha', hb, hc⟩