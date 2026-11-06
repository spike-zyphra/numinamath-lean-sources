import Mathlib

theorem algebra_16054 (x : ℕ) (hx : x > 0) (h : 4 * x = 2 * (50 + 10)) :
    x^2 - 50 * 10 = 400 := by
  have hx_eq : x = 30 := by 
    omega
  subst hx_eq
  all_goals 
    omega