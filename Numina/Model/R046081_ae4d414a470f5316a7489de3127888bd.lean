import Mathlib

theorem number_theory_23339 (b : ℕ) (hb : b ≥ 1) :
    (Nat.ofDigits b [5]) * (Nat.ofDigits b [3, 2]) = Nat.ofDigits b [1, 5, 1] ↔ b = 7 := by
  constructor
  · -- Assume (Nat.ofDigits b [5]) * (Nat.ofDigits b [3, 2]) = Nat.ofDigits b [1, 5, 1], prove b = 7
    intro h
    simp [Nat.ofDigits, List.foldl] at h 
    by_cases h1 : b ≤ 10
    · -- If b ≤ 10, then try all possible bases from 1 to 10.
      interval_cases b <;> omega 
    · -- If b > 10, prove that no solution exists. 
      have h2 : b > 10 := by linarith
      nlinarith [show b ≥ 1 from hb]
  · -- Assume b = 7, prove (Nat.ofDigits b [5]) * (Nat.ofDigits b [3, 2]) = Nat.ofDigits b [1, 5, 1]
    intro h 
    rw [h]
    all_goals
      norm_num [Nat.ofDigits, List.foldl]