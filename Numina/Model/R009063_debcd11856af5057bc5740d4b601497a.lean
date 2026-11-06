import Mathlib

theorem number_theory_19616  :
    IsGreatest {k : ℕ | k < 1000 ∧ k % 3 = 1 ∧ k % 4 = 1 ∧ k % 5 = 1 ∧ k % 6 = 1 ∧ k % 7 = 1} 841 := by
  constructor
  · -- Show 841 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 841 is the greatest
    intro k hk
    rcases hk with ⟨h1, h2, h3, h4, h5, h6⟩
    by_contra h
    push_neg at h
    interval_cases k <;> omega