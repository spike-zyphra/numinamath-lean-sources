import Mathlib

theorem inequalities_2088 {a b : ℝ} (ha : -1 < a) (hb : -1 < b) (h : b < a ∧ a < 0) :
    a - 1 < a + b ∧ a + b < a - b ∧ a - b < a + 1 := by
  have h1 : b < a := h.1
  have h2 : a < 0 := h.2
  
  have h3 : a - 1 < a + b := by
    linarith
  
  have h4 : a + b < a - b := by
    linarith
  
  have h5 : a - b < a + 1 := by
    linarith
  
  exact ⟨h3, h4, h5⟩