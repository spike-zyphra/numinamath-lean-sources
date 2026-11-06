import Mathlib

theorem number_theory_141348 :
    IsLeast {n | ∃ k, n = k + (k + 1) + (k + 2) ∧ 9 ∣ k ∧ 8 ∣ k + 1 ∧ 7 ∣ k + 2} 1488 := by
  constructor
  · -- First part: show 1488 is in the set.
    use 495
    all_goals norm_num
  · -- Second part: show there is no smaller element in the set.
    intro n hn
    rcases hn with ⟨k, hn_eq, hk1, hk2, hk3⟩
    omega