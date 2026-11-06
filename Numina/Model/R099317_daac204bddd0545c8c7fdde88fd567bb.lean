import Mathlib

theorem algebra_9670 : {x : ℝ | (x^2 - 2*x - 10)^2 + 2*(x^2 - 2*x) = 55} = {-1, 3, -3, 5} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward directions: if ((x ^ 2 - 2 * x - 10) ^ 2) + 2 * ((x ^ 2 - 2 * x) = 55), then x = -1, 0, 3, -3 or 5.
    intro h
    have h1 : (x^2 - 2*x - 10)^2 + 2*(x^2 - 2*x) = 55 := h
    have h2 : (x - 5) * (x + 3) * (x - 3) * (x + 1) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 2 * x), sq_nonneg (x ^ 2 - 2 * x - 10),
        sq_nonneg (x - 1), sq_nonneg (x - 1 - 4), sq_nonneg (x - 1 - 2),
        sq_nonneg (x - 1 + 2), sq_nonneg (x - 1 + 4)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case x - 5 = 0 => x = 5
      right
      right
      right
      linarith
    · -- Case x + 3 = 0 => x = -3
      right
      right
      left
      linarith
    · -- Case x - 3 = 0 => x = 3
      right
      left
      linarith
    · -- Case x + 1 = 0 => x = -1
      left
      linarith
  · -- Reverse direction: if x = -1, 0, 3, -3 or 5, then (x ^ 2 - 2*x - 10)^2 + 2*(x ^ 2 - 2*x) = 55
    rintro (rfl | rfl | rfl | rfl)
    · norm_num
    · norm_num
    · norm_num
    · norm_num