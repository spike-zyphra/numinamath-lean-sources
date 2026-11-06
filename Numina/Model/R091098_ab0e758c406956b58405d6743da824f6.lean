import Mathlib

theorem algebra_210081 {x : ℕ} (hx : x ≤ 63) (h : 54 + x = 2 * (63 - x)) :
    x = 24 := by 
  omega