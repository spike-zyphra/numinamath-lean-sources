import Mathlib

theorem number_theory_327749 (a b : ℤ) (h : ¬ 5 ∣ a) (h' : ¬ 5 ∣ b)
    (h'' : 5 ∣ a + b) :
    ¬ 5 ∣ 2 * a + 3 * b := by 
  omega