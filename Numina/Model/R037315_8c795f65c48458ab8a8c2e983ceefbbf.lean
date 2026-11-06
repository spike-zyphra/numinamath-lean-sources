import Mathlib
theorem algebra_608211 (x y : ℝ) : 8 * y ^ 4 + 4 * x ^ 2 * y ^ 2 + 4 * x * y ^ 2 + 2 * x ^ 3 + 2 * y ^ 2 + 2 * x = x ^ 2 + 1 ↔ x + 2 * y ^ 2 = 1 / 2:= by

  constructor
  · -- Forward direction: equation implies x + 2y² = 1/2.
    intro h
    have h1 : (x + 2 * y ^ 2 - 1 / 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x + 2 * y ^ 2 - 1 / 2), sq_nonneg (y ^ 2 + x - 1 / 2), sq_nonneg (2 * y ^ 2 - x), sq_nonneg (y ^ 2 - (x - 1 / 2)), sq_nonneg (4 * y ^ 2 - (x - 1 / 2)), sq_nonneg (x + 2 * y ^ 2 - 1 / 2)]
    have h2 : x + 2 * y ^ 2 - 1 / 2 = 0 := by
      rw [sq_eq_zero_iff] at h1
      linarith
    linarith
  · -- Backward direction: x + 2y² = 1/2 implies the equation.
    intro h
    have h1 : x + 2 * y ^ 2 = 1 / 2 := h
    have eq1 : 2 * y ^ 2 = 1 / 2 - x := by
      linarith
    have eq2 : y ^ 2 = (1 / 2 - x) / 2 := by
      linarith
    have eq3 : y ^ 4 = ((1 / 2 - x) / 2) ^ 2 := by
      calc
        y ^ 4 = (y ^ 2) ^ 2 := by ring
        _ = ((1 / 2 - x) / 2) ^ 2 := by rw [eq2]
    nlinarith [eq1, eq2, eq3, sq_nonneg (x - 1 / 2), sq_nonneg (y ^ 2 - (1 - x)), sq_nonneg (y ^ 2 - 0), sq_nonneg (x - 0), sq_nonneg (x - 1), sq_nonneg (y ^ 2 - 1 / 4)]