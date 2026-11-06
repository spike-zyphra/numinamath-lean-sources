import Mathlib

def smile (a b : ℤ) := a * b + 3 * a + b

theorem algebra_251647 {x : ℤ} (hx : (smile x 5) * 6 = 72123) : x = 1001 := by
  simp [smile] at hx 
  omega