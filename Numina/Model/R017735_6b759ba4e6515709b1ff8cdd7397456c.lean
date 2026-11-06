import Mathlib

theorem algebra_253037 (x y z : ℝ) (h1 : x + y + z = 12) (h2 : x^2 + y^2 + z^2 = 54) :
    9 ≤ x * y ∧ x * y ≤ 25 := by 
  have h3 : x + y + z = 12 := h1
  have h4 : x ^ 2 + y ^ 2 + z ^ 2 = 54 := h2
  have h5 : 2 * (x * y + x * z + y * z) = 90 := by
    have eq1 : (x + y + z) ^ 2 = x^2 + y^2 + z^2 + 2 * (x * y + x * z + y * z) := by
      ring
    rw [h1, h2] at eq1
    linarith
  have h6 : x * y + x * z + y * z = 45 := by
    linarith
  constructor
  · -- Prove 9 ≤ x * y
    nlinarith [sq_nonneg (x - y), sq_nonneg (z - 6), sq_nonneg (x + y - 6),
              sq_nonneg (z), sq_nonneg (x - y)]
  · -- Prove x * y ≤ 25
    nlinarith [sq_nonneg (x - y), sq_nonneg (z - 2), sq_nonneg (z - 6), sq_nonneg (x + y - 10),
              sq_nonneg (x - 5), sq_nonneg (y - 5)]