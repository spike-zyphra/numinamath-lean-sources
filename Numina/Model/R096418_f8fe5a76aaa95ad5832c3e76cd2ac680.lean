import Mathlib

theorem number_theory_237746 (a b c : ℕ) (h : 37 ∣ 100 * a + 10 * b + c) :
    37 ∣ 100 * b + 10 * c + a + 100 * c + 10 * a + b := by
  omega