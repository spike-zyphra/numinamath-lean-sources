import Mathlib


open Nat


theorem number_theory_234715 (n : ℕ) (h : n > 0) (a b c d : ℕ)
    (ha : a + b + c + d = n) (hb : 1 * a + 5 * b + 10 * c + 20 * d = 13 * n)
    (hc : 1 * a + 5 * b + 10 * c + 20 * d - 1 = 14 * (n - 1)) :
    c = 0 := by
  have h3 : n = 13 := by
    have hnS : 1 * a + 5 * b + 10 * c + 20 * d = 13 * n := hb
    have hnS' : (1 * a + 5 * b + 10 * c + 20 * d) - 1 = 14 * (n - 1) := hc
    have h4 : 1 * a + 5 * b + 10 * c + 20 * d ≥ 1 := by
      omega
    have h5 : n ≥ 1 := by
      omega
    have eq2 : 13 * n - 1 = 14 * (n - 1) := by
      omega
    omega
  have eq3 : a + b + c + d = 13 := by
    rw [h3] at ha
    omega
  have eq4 : 1 * a + 5 * b + 10 * c + 20 * d = 169 := by
    rw [h3] at hb
    all_goals omega
  have h4 : c ≤ 13 := by
    omega
  interval_cases c <;> omega