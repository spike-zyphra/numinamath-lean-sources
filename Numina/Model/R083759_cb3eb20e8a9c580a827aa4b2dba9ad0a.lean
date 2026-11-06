import Mathlib

theorem number_theory_1659 : IsLeast {n : ℕ | 0 < n ∧ 2 ∣ n ∧ 4 ∣ n ∧ 7 ∣ n ∧ 8 ∣ n ∧ ∃ k, n = k ^ 2} 784 := by
  constructor
  · -- Let's show that 784 is in our set.
    constructor
    · norm_num -- 784 > 0
    constructor
    · norm_num -- 2 divides 784
    constructor
    · norm_num -- 4 divides 784
    constructor
    · norm_num -- 7 divides 784
    constructor
    · norm_num -- 8 divides 784
    · -- There exists k such that 784 = k^2
      use 28
      all_goals norm_num
  · -- Now, we need to show that 784 is the smallest
    intro n hn
    rcases hn with ⟨hn_pos, hn_div_2, hn_div_4, hn_div_7, hn_div_8, ⟨k, rfl⟩⟩
    have h1 : k ^ 2 > 0 := by
      nlinarith
    have h9 : (k ^ 2) ≥ 784 := by
      by_contra h
      push_neg at h
      have h5 : k ≤ 27 := by nlinarith
      interval_cases k <;> norm_num at *
      all_goals omega
    linarith