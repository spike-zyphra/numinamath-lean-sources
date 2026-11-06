import Mathlib

theorem algebra_118313 {x y : ℕ} (h : x + y = 70) (h1 : x = 4 * y + 5) :
    x = 57 ∧ y = 13 := by
  have eq1 : x + y = 70 := h
  have eq2 : x = 4 * y + 5 := h1
  have hy : y = 13 := by 
    omega 
  have hx : x = 57 := by 
    omega 
  exact ⟨hx, hy⟩