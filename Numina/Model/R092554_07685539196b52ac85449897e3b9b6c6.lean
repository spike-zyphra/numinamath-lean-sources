import Mathlib

theorem algebra_295833 (x : ℚ) : 5 * x ^ 3 + 3 * x ^ 2 + 3 * x - 2 = 0 ↔ x = 2 / 5 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 2/5
    intro h
    have h1 : 5 * x ^ 3 + 3 * x ^ 2 + 3 * x - 2 = 0 := h
    have h2 : (x - 2 / 5) * (5 * x ^ 2 + 5 * x + 5) = 0 := by
      ring_nf at h1 ⊢
      linarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case where x - 2/5 = 0
      linarith
    · -- Case where 5x^2 + 5x + 5 = 0, which leads to a contradiction
      have h5 : 5 * x ^ 2 + 5 * x + 5 = 0 := by
        linarith
      have : 5 * x ^ 2 + 5 * x + 5 ≠ 0 := by
        intro h'
        have : x ^ 2 + x + 1 = 0 := by 
          linarith
        have h7 : x ^ 2 + x + 1 > 0 := by
          nlinarith [sq_nonneg (x + 1 / 2)]
        linarith
      contradiction
  · -- Backward direction: if x = 2/5, then the equation holds
    intro h
    rw [h]
    norm_num