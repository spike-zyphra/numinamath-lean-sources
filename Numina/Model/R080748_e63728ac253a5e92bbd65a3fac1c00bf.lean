import Mathlib

theorem number_theory_264738 (P Q : ℕ) (h : P < 10) (h' : Q < 10)
    (h'' : (10 * P + Q) * (100 * P + 10 * Q + Q) = 32951) :
    P + Q = 15 := by
  interval_cases P <;> interval_cases Q
    <;> omega