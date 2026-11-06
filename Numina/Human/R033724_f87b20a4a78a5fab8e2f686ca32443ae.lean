import Mathlib

theorem algebra_166621 :
    {x : ℝ | ∑ i ∈ Finset.range 10, (x + i) * (x + i + 1) = ∑ i ∈ Finset.range 9, (i + 1) * (i + 2)} = {0, -10} := by
  ext x
  constructor
  · intro h
    simp [Finset.sum_range_succ, add_mul, mul_add] at h
    have : x * (x + 10) = 0 := by linarith
    cases' (mul_eq_zero.mp this) with hx hx
    · left; exact hx
    · right; simp; linarith
  · rintro (h | h)
    · rw [h]
      norm_num [Finset.sum_range_succ, add_mul, mul_add]
    · rw [h]
      norm_num [Finset.sum_range_succ, add_mul, mul_add]