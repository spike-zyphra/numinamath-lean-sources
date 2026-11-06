import Mathlib

theorem algebra_13883 : IsLeast {n : ℕ | 500 + 8 * 15 * n < (8 * 3.1 * 5 * n : ℝ)} 126 := by 
  constructor
  · -- Show 126 is in the set
    norm_num
  · -- Show it's the smallest
    intro n hn
    have h : 500 + (8 * 15 * (n : ℝ)) < (8 * 3.1 * 5 * (n : ℝ)) := by
      simpa using hn
    by_contra h'
    push_neg at h'
    have h1 : n ≤ 125 := by linarith
    have h2 : (n : ℝ) ≤ (125 : ℝ) := by exact_mod_cast h1
    nlinarith