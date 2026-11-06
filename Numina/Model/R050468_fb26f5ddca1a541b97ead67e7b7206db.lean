import Mathlib

theorem number_theory_280900 (n : ℕ) (h₀ : n = 64) :
    IsLeast {k | ∃ m, m = n / 2 ^ k ∧ m = 1} 6 := by
  rw [h₀]
  constructor
  · -- 6 is in the set
    use 1
    all_goals norm_num
  · -- minimality of 6
    intro k hk
    rcases hk with ⟨m, hm1, hm2⟩
    have h1 : 64 / 2 ^ k = 1 := by 
      linarith [hm1, hm2]
    by_contra h
    push_neg at h
    interval_cases k <;> norm_num at h1 <;> omega