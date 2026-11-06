import Mathlib

theorem algebra_318813 (x y z : ℝ) (h₀ : x + y + z = 1) (h₁ : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
    -1 ≤ x * y * z ∧ x * y * z ≤ 5 / 27 := by

  have h2 : x * y + y * z + z * x = -1 := by
    have h2 : x + y + z = 1 := h₀
    have h3 : x ^ 2 + y ^ 2 + z ^ 2 = 3 := h₁
    have h4 : (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by ring
    rw [h2, h3] at h4
    linarith

  have h5 : x * y * z = x * (x ^ 2 - x - 1) := by
    have h6 : y * z = x ^ 2 - x - 1 := by
      have h7 : x * y + y * z + z * x = -1 := h2
      have h8 : y * z = -1 - x * (y + z) := by linarith
      have h9 : y + z = 1 - x := by linarith
      rw [h9] at h8
      linarith
    have h10 : x * y * z = x * (y * z) := by ring
    rw [h10, h6]

  have h6 : -1 ≤ x := by
    nlinarith [sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z)]

  have h7 : x ≤ 5 / 3 := by
    nlinarith [sq_nonneg (y - z), sq_nonneg (x - y), sq_nonneg (x - z)]

  constructor
  · -- Proof of -1 ≤ x * y * z
    rw [h5]
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1/3), sq_nonneg (x - 5/3), sq_nonneg (x - 1), sq_nonneg (x + 1)]

  · -- Proof of x * y * z ≤ 5 / 27
    rw [h5]
    nlinarith [sq_nonneg (x - 1/3), sq_nonneg (x - 5/3), sq_nonneg (x - 1), sq_nonneg (x + 1/3), sq_nonneg (x - 5/3)]