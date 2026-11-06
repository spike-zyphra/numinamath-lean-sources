import Mathlib

theorem number_theory_225854 :
    IsGreatest {n | 0 < n ∧ n < 10000 ∧ 7 ∣ n ∧ ∃ k, n = (k ^ 2) + ((k + 1) ^ 2) + ((k + 2) ^ 2)} 8750 := by
  constructor
  · constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    use 53
    all_goals norm_num
    <;> rfl
  · -- Assume n is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_lt, hn_div, ⟨k, h_eq⟩⟩
    by_contra h
    push_neg at h
    have h1 : k < 100 := by
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg (k + 1 : ℕ), sq_nonneg (k + 2 : ℕ)]

    interval_cases k <;> omega
    all_goals
      omega
      <;> norm_num at h_eq
      <;> omega