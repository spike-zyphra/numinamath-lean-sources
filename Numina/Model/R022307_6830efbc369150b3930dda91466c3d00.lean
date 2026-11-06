import Mathlib

theorem algebra_321075 {x : ℕ} (hx : x > 0) (h1 : 5 * 10 = x * 12) (h2 : 7 * 8 = x * 10) :
    IsLeast {n | n > 0 ∧ 3 * n = x * 15} 24 := by 
  exfalso
  omega