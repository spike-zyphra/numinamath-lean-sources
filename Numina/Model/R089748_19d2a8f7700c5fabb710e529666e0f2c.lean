import Mathlib

theorem algebra_18967 : ∑ᶠ x ∈ {x : ℝ | 2 * x * (x - 10) = -50}, x = 5 := by
  have h1 : {x : ℝ | 2 * x * (x - 10) = -50} = {5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Forward implication: if 2x(x-10) = -50, then x = 5
      intro h2
      have h3 : 2 * x ^ 2 - 20 * x + 50 = 0 := by
        nlinarith
      have h4 : (x - 5) ^ 2 = 0 := by
        nlinarith
      have h5 : x - 5 = 0 := by
        nlinarith
      linarith
    · -- Backward implication: if x = 5, then 2x(x-10) = -50
      intro h5
      rw [h5]
      norm_num
  rw [h1]
  simp