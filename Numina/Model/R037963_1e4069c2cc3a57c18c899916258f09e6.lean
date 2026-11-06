import Mathlib

theorem algebra_22411 : IsGreatest {x : ℤ | 0 ≤ 3620 + 322 * x - 4 * x ^ 2} 90 := by
  constructor
  · -- Show that 90 is in the set
    norm_num
  · -- Show that any element in the set is ≤ 90
    intro x h
    have h1 : 0 ≤ 3620 + 322 * x - 4 * x ^ 2 := h
    by_contra h2
    push_neg at h2
    have h2 : x ≥ 91 := by omega
    have h3 : 3620 + 322 * x - 4 * x ^ 2 < 0 := by
      nlinarith [sq_nonneg (x - 90 : ℤ), sq_nonneg (x - 91 : ℤ)]
    linarith