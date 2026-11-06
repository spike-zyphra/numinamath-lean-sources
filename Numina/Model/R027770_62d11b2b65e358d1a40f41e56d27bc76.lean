import Mathlib

theorem algebra_229116 {x y : ℕ} (h : x * 27 = y * 65 + 34) (h' : y ≤ 44) :
    x + y = 66 := by 
  have h1 : y ≤ 44 := h'
  have h2 : x ≤ 107 := by 
    nlinarith [h, h']
  interval_cases y <;> omega