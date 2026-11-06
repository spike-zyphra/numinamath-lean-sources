import Mathlib

theorem algebra_19787 (x : ℝ) (hx : x ≠ -5 / 3) (h : (x + 6) * 2 = 3 * x + 5) :
    (x + 6) * 2 * Real.pi = 26 * Real.pi := by 
  have hx_eq : x = 7 := by 
    linarith 
  rw [hx_eq] 
  ring