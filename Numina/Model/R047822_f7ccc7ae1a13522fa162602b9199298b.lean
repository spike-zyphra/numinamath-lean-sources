import Mathlib
theorem algebra_609110 : IsLeast {n : ℕ | ((5 : ℝ) ^ (n + 1) + 2 ^ (n + 1)) / (5 ^ n + 2 ^ n) > 4.99} 7:= by
  constructor
  · -- Prove 7 is in the set.
    norm_num
  · -- Prove no number less than 7 is in the set.
    intro n hn
    have h : ((5 : ℝ) ^ (n + 1) + 2 ^ (n + 1)) / (5 ^ n + 2 ^ n) > 4.99 := by
      simpa using hn
    by_contra h1
    push_neg at h1
    have h2 : n < 7 := h1
    interval_cases n <;> norm_num at h ⊢ <;> try { all_goals norm_num at h ⊢; all_goals linarith }