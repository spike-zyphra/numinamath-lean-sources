import Mathlib
theorem algebra_13519 : IsLeast {k | 3 * 2 ^ k > 100} 6 := by
  constructor
  · -- Show 6 is in the set
    norm_num
  · -- Show 6 is minimal, i.e., no smaller element is in the set
    intro k hk
    have h : 3 * 2 ^ k > 100 := hk
    by_contra h'
    push_neg at h'
    have h1 : k < 6 := by linarith
    have h2 : 3 * 2 ^ k ≤ 100 := by
      interval_cases k <;> norm_num
      <;> all_goals omega
    linarith