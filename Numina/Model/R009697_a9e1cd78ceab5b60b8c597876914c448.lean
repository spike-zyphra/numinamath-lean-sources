import Mathlib
theorem algebra_822 (P : ℕ → ℝ) (hP : ∀ n, P n = 1000 * (1 + 0.05) ^ n) :
    IsLeast {n | P n > 2000} 15 := by
  constructor
  · -- Show that 15 is indeed in the set
    show P 15 > 2000
    rw [hP 15]
    norm_num
  · -- Show that 15 is the smallest such integer in the set
    intro n hn
    have h : P n > 2000 := hn
    rw [hP n] at h
    by_contra h'
    push_neg at h'
    interval_cases n <;> norm_num at h ⊢ <;> all_goals
      norm_num [hP] at h ⊢
      all_goals linarith