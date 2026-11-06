import Mathlib
theorem Algebra_9456 (m : ℝ) (h : ¬∃x > 0, m * x ^ 2 + 2 * x + m > 0) : m ≤ -1 := by 
  by_contra h1
  push_neg at h1
  have h2 : ∃x > 0, m * x ^ 2 + 2 * x + m > 0 := by
    use 1
    constructor 
    · norm_num
    · -- show m * 1 ^ 2 + 2 * 1 + m > 0
      nlinarith
  contradiction