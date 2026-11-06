import Mathlib

theorem number_theory_233271 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : 72 ∣ Nat.ofDigits 10 [b, 4, a, 2, 4]) :
    (a = 8 ∧ b = 0) ∨ (a = 0 ∧ b = 8) := by 
  simp [Nat.ofDigits, List.foldl] at h
  interval_cases a <;> interval_cases b <;> omega