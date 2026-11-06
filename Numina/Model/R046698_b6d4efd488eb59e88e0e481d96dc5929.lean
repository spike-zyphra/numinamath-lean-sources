import Mathlib

theorem algebra_18829 : IsLeast {n : ℤ | (2 * n - 13.7 : ℝ) > 125.28} 70 := by 
  constructor
  · -- Show that 70 is in the set.
    norm_num
  · -- Show that no integer smaller than 70 is in the set.
    intro n hn
    have h : (2 * n - 13.7 : ℝ) > 125.28 := by 
      simpa using hn
    by_contra h'
    push_neg at h'
    have h1 : n ≤ 69 := by omega
    have h2 : (n : ℝ) ≤ (69 : ℝ) := by exact_mod_cast h1
    nlinarith