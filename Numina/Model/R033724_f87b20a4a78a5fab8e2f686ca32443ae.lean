import Mathlib

theorem algebra_166621 :
    {x : ℝ | ∑ i ∈ Finset.range 10, (x + i) * (x + i + 1) = ∑ i ∈ Finset.range 9, (i + 1) * (i + 2)} = {0, -10} := by
  ext x
  simp only [Finset.sum_range_succ, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume the equality of sums holds, prove x ∈ {0, -10}
    intro h
    norm_num [Finset.sum_range_succ] at h ⊢
    have h1 : (x : ℝ) * (x + 10) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- case x * (x + 10) = 0 because x = 0
      left
      linarith
    · -- case x * (x + 10) = 0 because x + 10 = 0
      right
      linarith
  · -- Assume x ∈ {0, -10}, prove the equality of sums
    rintro (rfl | rfl)
    · -- x = 0
      norm_num [Finset.sum_range_succ]
    · -- x = -10
      norm_num [Finset.sum_range_succ]