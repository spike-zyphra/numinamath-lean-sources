import Mathlib

theorem algebra_144407 (x y z n : ℤ) (h₀ : x * y + y * z + z * x = 3 * n ^ 2 - 1)
    (h₁ : x + y + z = 3 * n) (h₂ : x ≥ y ∧ y ≥ z) :
    x = n + 1 ∧ y = n ∧ z = n - 1 := by

  have h3 : z = 3 * n - x - y := by
    linarith
  rw [h3] at h₀

  have hx : x = n + 1 := by
    nlinarith [sq_nonneg (x - (n + 1)), sq_nonneg (y - n), 
            sq_nonneg ((3 * n - x - y) - (n - 1)), 
            sq_nonneg (x - y), sq_nonneg (y - (n + 1)), sq_nonneg (x - (n - 1)), 
            h₂.1, h₂.2, sq_nonneg ((3 * n - x - y) - y)]

  have h5 : y = n := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - n), sq_nonneg ((3 * n - x - y) - (n - 1)), 
            sq_nonneg ((3 * n - x - y) - y), sq_nonneg (y - n), h₂.1, h₂.2]

  have hz : z = n - 1 := by
    linarith [h3, hx, h5]

  constructor
  · exact hx
  constructor
  · exact h5
  · exact hz