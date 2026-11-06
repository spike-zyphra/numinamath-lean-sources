import Mathlib

theorem number_theory_130980 {x y : ℕ} (hy : y ≠ 0) (h : x * 10 + 1 = 189 ∧ x * 10 + 7 = 147) :
    x = 21 ∧ y = 7 := by 
  have h1 : x * 10 + 1 = 189 := h.1
  have h2 : x * 10 + 7 = 147 := h.2
  have eq1 : x * 10 = 188 := by 
    omega 
  have eq2 : x * 10 = 140 := by 
    omega 
  omega