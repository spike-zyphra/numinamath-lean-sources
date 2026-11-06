import Mathlib

theorem algebra_104688 {x y : ℝ} (h : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 1) :
    x + y = 0 := by

  have h1 : (x + Real.sqrt (1 + x ^ 2)) ≠ 0 := by
    by_contra h1
    have : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 0 := by
      rw [h1]
      norm_num
    linarith

  have h2 : (y + Real.sqrt (1 + y ^ 2)) ≠ 0 := by
    by_contra h2
    have : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 0 := by
      rw [h2]
      norm_num
    linarith

  have h3 : y + Real.sqrt (1 + y ^ 2) = Real.sqrt (1 + x ^ 2) - x := by
    have h3 : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 1 := h

    have h4 : (x + Real.sqrt (1 + x ^ 2)) * (Real.sqrt (1 + x ^ 2) - x) = 1 := by
      nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sq_sqrt (show (1 + x ^ 2 : ℝ) ≥ 0 by nlinarith)]

    have h5 : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) =
          (x + Real.sqrt (1 + x ^ 2)) * (Real.sqrt (1 + x ^ 2) - x) := by
      linarith [h3, h4]

    have h6 : (x + Real.sqrt (1 + x ^ 2)) ≠ 0 := h1
    have h7 : y + Real.sqrt (1 + y ^ 2) = Real.sqrt (1 + x ^ 2) - x := by
      apply (mul_left_inj' h6).mp
      linarith
    exact h7

  have h4 : x + Real.sqrt (1 + x ^ 2) = Real.sqrt (1 + y ^ 2) - y := by
    have h3 : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) = 1 := h

    have h8 : (y + Real.sqrt (1 + y ^ 2)) * (Real.sqrt (1 + y ^ 2) - y) = 1 := by
      nlinarith [Real.sqrt_nonneg (1 + y ^ 2), Real.sq_sqrt (show (1 + y ^ 2 : ℝ) ≥ 0 by nlinarith)]

    have h9 : (x + Real.sqrt (1 + x ^ 2)) * (y + Real.sqrt (1 + y ^ 2)) =
          (y + Real.sqrt (1 + y ^ 2)) * (Real.sqrt (1 + y ^ 2) - y) := by
      linarith [h3, h8]

    have h7 : (y + Real.sqrt (1 + y ^ 2)) ≠ 0 := h2
    have h8 : x + Real.sqrt (1 + x ^ 2) = Real.sqrt (1 + y ^ 2) - y := by
      apply (mul_left_inj' h7).mp
      linarith
    exact h8

  nlinarith [Real.sqrt_nonneg (1 + x ^ 2), Real.sqrt_nonneg (1 + y ^ 2),
            Real.sq_sqrt (show (1 + x ^ 2 : ℝ) ≥ 0 by nlinarith),
            Real.sq_sqrt (show (1 + y ^ 2 : ℝ) ≥ 0 by nlinarith)
          ]