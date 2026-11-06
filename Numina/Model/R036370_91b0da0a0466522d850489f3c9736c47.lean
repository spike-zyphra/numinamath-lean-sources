import Mathlib

theorem number_theory_5424 (x : ZMod 3) : (x ^ 2) = 1 ↔ x = 1 ∨ x = 2 := by 
  have h1 : x = 0 ∨ x = 1 ∨ x = 2 := by 
    fin_cases x <;> simp 
  rcases h1 with (h | h | h)
  · -- x = 0 
    rw [h]
    native_decide 
  · -- x = 1 
    rw [h]
    native_decide 
  · -- x = 2 
    rw [h]
    native_decide