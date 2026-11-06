import Mathlib

theorem algebra_99037 {a b : ℤ} (ha : a > 0) (hb : b > 0)
    (h : |(36 * a - 81 * b)| = 4 * 242) :
    a + b = 7 ∧ b = 3 ∨ a + b = 10 ∧ b = 1 := by 
  exfalso
  have h1 : (36 * a - 81 * b) % 9 = 0 := by
    omega
  have h2 : |(36 * a - 81 * b)| % 9 = 5 := by 
    omega
  have h3 : |(36 * a - 81 * b)| % 9 = 0 := by
    have h4 : (36 * a - 81 * b) % 9 = 0 := h1
    cases' abs_cases (36 * a - 81 * b) with h5 h5 
    · 
      omega
    · 
      omega
  omega