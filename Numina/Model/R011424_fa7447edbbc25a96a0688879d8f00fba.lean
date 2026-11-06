import Mathlib

theorem algebra_1450 : {x : ℝ | x ^ 2 - 5 * x + 6 = 0} = {2, 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume x ∈ {x : ℝ | x ^ 2 - 5 * x + 6 = 0}, prove x ∈ {2, 3}
    intro h
    have h1 : x ^ 2 - 5 * x + 6 = 0 := h
    have h2 : (x - 2) * (x - 3) = 0 := by 
      linarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case x - 2 = 0
      left
      linarith
    · -- Case x - 3 = 0
      right
      linarith
  · -- Assume x ∈ {2, 3}, prove x ∈ {x : ℝ | x ^ 2 - 5 * x + 6 = 0}
    rintro (h | h)
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = 3
      rw [h]
      norm_num