import Mathlib

theorem algebra_111298 (n : ℤ) : n^5 - 2 * n^4 - 7 * n^2 - 7 * n + 3 = 0 ↔ n = -1 ∨ n = 3 := by
  constructor
  · -- Assume n^5 - 2 * n^4 - 7 * n^2 - 7 * n + 3 = 0, prove n = -1 ∨ n = 3
    intro h
    have h1 : n^5 - 2 * n^4 - 7 * n^2 - 7 * n + 3 = 0 := h
    have eq1 : (n + 1) * (n - 3) * (n ^ 3 + 3 * n - 1) = n ^ 5 - 2 * n ^ 4 - 7 * n ^ 2 - 7 * n + 3 := by ring
    have h2 : (n + 1) * (n - 3) * (n ^ 3 + 3 * n - 1) = 0 := by 
      rw [eq1] at *
      all_goals linarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case (n + 1) * (n - 3) = 0
      cases' (mul_eq_zero.mp h3) with h5 h6
      · -- Case n + 1 = 0
        left
        linarith
      · -- Case n - 3 = 0
        right
        linarith
    · -- Case n^3 + 3 * n - 1 = 0
      have h3 : n^3 + 3 * n - 1 = 0 := by linarith
      have h4 : n ≤ 1 := by 
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n * (n + 1)), sq_nonneg (n - 1), sq_nonneg (n ^ 2 - 1)]
      have h5 : n ≥ -2 := by 
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n * (n + 1)), sq_nonneg (n - 1), sq_nonneg (n ^ 2 - 1)]
      interval_cases n <;> omega
  · -- Assume n = -1 ∨ n = 3, prove n^5 - 2 * n^4 - 7 * n^2 - 7 * n + 3 = 0
    rintro (h | h)
    · -- Case n = -1
      rw [h]
      norm_num
    · -- Case n = 3
      rw [h]
      norm_num