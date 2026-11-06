import Mathlib

theorem algebra_147195 : {x : ℕ | ∑ i ∈ Finset.range 12, (i + 1) * x = 1014} = {13} := by
  ext x
  simp only [Finset.sum_range_succ, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume the sum equals 1014, prove x = 13
    intro h
    norm_num [Finset.sum_range_succ] at h
    omega
  · -- Assume x = 13, prove the sum equals 1014
    intro h
    rw [h]
    norm_num [Finset.sum_range_succ]