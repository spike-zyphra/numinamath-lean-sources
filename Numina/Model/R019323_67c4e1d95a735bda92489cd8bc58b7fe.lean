import Mathlib


open Real


theorem algebra_115639 (x y z : ℝ) (h₀ : x + 2 * y + 3 * z = 1) (h₁ : y * z + z * x + x * y = -1) :
    (3 - 3 * √3) / 4 ≤ x + y + z ∧ x + y + z ≤ (3 + 3 * √3) / 4 := by


  have eq2 : 3 * z ^ 2 - (3 - 4 * (x + y + z)) * z + 2 * (x + y + z) ^ 2 - 3 * (x + y + z) = 0 := by
    have h3 : x + 2 * y + 3 * z = 1 := h₀
    have h4 : y * z + z * x + x * y = -1 := h₁
    have h3' : x + y = (x + y + z) - z := by linarith
    have hy : y = 1 - (x + y + z) - 2 * z := by
      have eq1 : x + 2 * y = 1 - 3 * z := by linarith [h₀]
      have eq2 : x + 2 * y = (x + y) + y := by ring
      rw [eq2] at eq1
      rw [h3'] at eq1
      nlinarith
    have hx : x = 2 * (x + y + z) - 1 + z := by
      have h3' : x + y = (x + y + z) - z := by linarith
      linarith [h3', hy]
    have eq2 : (2 * (x + y + z) - 1 + z) * (1 - (x + y + z) - 2 * z) + (1 - (x + y + z) - 2 * z) * z + z * (2 * (x + y + z) - 1 + z) = -1 := by
      rw [show x = 2 * (x + y + z) - 1 + z by linarith [hx], show y = 1 - (x + y + z) - 2 * z by linarith [hy]] at h₁
      nlinarith
    nlinarith [sq_nonneg (z - 1), sq_nonneg ((x + y + z) - 1), sq_nonneg (z - (x + y + z) + 1), sq_nonneg (z - (x + y + z) - 1) ]


  have h8 : (3 - 4 * (x + y + z)) ^ 2 - 4 * (3) * (2 * (x + y + z) ^ 2 - 3 * (x + y + z)) ≥ 0 := by
    nlinarith [ sq_nonneg (3 * z - (3 - 4 * (x + y + z)) / 2 ), sq_nonneg (z - ( (3 - 4 * (x + y + z)) ) / 6 ) ]

  have h11 : (3 - 4 * (x + y + z)) ^ 2 - 12 * (2 * (x + y + z) ^ 2 - 3 * (x + y + z)) = 9 + 12 * (x + y + z) - 8 * (x + y + z) ^ 2 := by
    nlinarith


  have h7 : (x + y + z) ≥ (3 - 3 * Real.sqrt 3) / 4 := by
    nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]

  have h7' : (x + y + z) ≤ (3 + 3 * Real.sqrt 3) / 4 := by
    nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]

  constructor
  · linarith
  · linarith