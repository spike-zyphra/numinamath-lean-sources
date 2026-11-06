import Mathlib

theorem number_theory_6022 (x1 x2 : ℕ) (hx1 : 0 < x1) (hx2 : 0 < x2)
    (h : 5 * x1 + 3 * x2 = 52) :
    (x1, x2) = (8, 4) ∨ (x1, x2) = (5, 9) ∨ (x1, x2) = (2, 14) := by
  have eq1 : x1 ≤ 10 := by 
    omega
  have eq2 : x2 ≤ 17 := by 
    omega
  
  have h1 : x1 = 2 ∨ x1 = 5 ∨ x1 = 8 := by 
    omega
  
  rcases h1 with (rfl | rfl | rfl)
  · -- Case x1 = 2
    have hx2' : x2 = 14 := by 
      omega 
    simp [hx2']
  
  · -- Case x1 = 5
    have hx2' : x2 = 9 := by 
      omega 
    simp [hx2']
  
  · -- Case x1 = 8
    have hx2' : x2 = 4 := by 
      omega 
    simp [hx2']