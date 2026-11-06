import Mathlib

theorem number_theory_192662 :
    IsLeast {N | N % 6 = 5 ∧ N % 5 = 4 ∧ N % 4 = 3 ∧ N % 3 = 2 ∧ N % 2 = 1} 59 := by
  constructor
  · -- First part: show 59 is in the set
    show (59 % 6 = 5) ∧ (59 % 5 = 4) ∧ (59 % 4 = 3) ∧ (59 % 3 = 2) ∧ (59 % 2 = 1)
    norm_num
  · -- Second part: show 59 is the smallest
    intro N hN
    rcases hN with ⟨h6, h5, h4, h3, h2⟩
    by_contra h
    push_neg at h
    interval_cases N <;> norm_num at h6 h5 h4 h3 h2 <;> omega