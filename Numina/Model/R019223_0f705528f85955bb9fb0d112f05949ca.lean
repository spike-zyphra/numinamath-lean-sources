import Mathlib

theorem number_theory_5207 {a b : ℕ} (ha : a ≠ b) (h : (10 * a + b) * 10 ^ 2014 = (10 * b + a) * 10 ^ 2014 + 3 * 10 ^ 2013) :
    a = 1 ∧ b = 2 ∨ a = 2 ∧ b = 1 := by 
  have h3 : 9 * (a : ℕ) * 10 ^ 2014 = 9 * (b : ℕ) * 10 ^ 2014 + 3 * 10 ^ 2013 := by 
    omega
  have h4 : 90 * (a : ℕ) * 10 ^ 2013 = 90 * (b : ℕ) * 10 ^ 2013 + 3 * 10 ^ 2013 := by
    nlinarith
  have h6 : 90 * (a : ℕ) = 90 * (b : ℕ) + 3 := by
    nlinarith
  omega