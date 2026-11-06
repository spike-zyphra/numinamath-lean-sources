import Mathlib

theorem algebra_21968 : {x : ℤ | x^6 - 2 * x^5 + 2 * x^3 - 2 * x + 1 = 292} = {3} := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x^6 - 2 * x^5 + 2 * x^3 - 2 * x + 1 = 292, prove x = 3
    intro h 
    have h1 : x^6 - 2 * x^5 + 2 * x^3 - 2 * x + 1 = 292 := h 
    have h2 : x ≤ 4 := by
      nlinarith [sq_nonneg (x ^ 2 - 3 * x), sq_nonneg (x - 3), sq_nonneg (x ^ 2 - 4), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x ^ 2 - x - 3), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x * (x - 3)), sq_nonneg ((x - 3) * (x + 1))]
    have h3 : x ≥ -2 := by
      nlinarith [sq_nonneg (x ^ 2 - 3 * x), sq_nonneg (x - 3), sq_nonneg (x ^ 2 - 4), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x ^ 2 - x - 3), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x * (x - 3)), sq_nonneg ((x - 3) * (x + 1))]
    interval_cases x <;> norm_num at h1 <;> omega 
  · -- Assume x = 3, prove x^6 - 2x^5 + 2x^3 - 2x + 1=292
    intro h 
    rw [h] 
    norm_num