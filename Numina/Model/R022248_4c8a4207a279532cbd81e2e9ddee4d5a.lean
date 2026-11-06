import Mathlib

theorem number_theory_99464 :
    IsLeast {n | ∃ k, n = k ∧ 8 ∣ n ∧ 7 ∣ n + 1 ∧ 6 ∣ n + 2 ∧ 5 ∣ n + 3} 832 := by
  constructor
  · -- Show that 832 is in the set
    use 832
    all_goals norm_num
  · -- Assume that there exists a n such that all of congruences relation holds
    intro n hn
    rcases hn with ⟨k, hk, h1, h2, h3, h4⟩
    omega