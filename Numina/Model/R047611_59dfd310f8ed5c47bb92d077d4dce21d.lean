import Mathlib

theorem number_theory_93865 (a b c : ℕ) (ha : a < 10) (hb : b < 10) (hc : 0 < c ∧ c < 10)
    (h : (7 * 100 + 10 * a + 2) - (4 * 100 + 8 * 10 + b) = (c * 100 + 7 * 10 + 3)) :
    a + b + c = 17 := by
  have h1 : (7 * 100 + 10 * a + 2) = (4 * 100 + 8 * 10 + b) + (c * 100 + 7 * 10 + 3) := by
    omega -- This is needed to convert from subtraction to addition. 
  have hc1 : c < 10 := by linarith
  have hc2 : c > 0 := by linarith
  have ha : a < 10 := by assumption
  have hb : b < 10 := by assumption
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega -- This handles the arithmetic