import Mathlib


theorem algebra_297690 (m : ℤ) (h : ∀ x : ℝ, 3 * x ^ 2 + m * x - 2 = 0 → x > -9 / 5 ∧ x < 3 / 7) :
    m = 4 := by

  have h1 := h ((- (m : ℝ) + Real.sqrt (m ^ 2 + 24)) / 6) (by
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 24 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (m ^ 2 + 24 : ℝ) by nlinarith)]
  )
  have h2 := h ((- (m : ℝ) - Real.sqrt (m ^ 2 + 24)) / 6) (by
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 24 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (m ^ 2 + 24 : ℝ) by nlinarith)]
  )

  have h3 : (- (m : ℝ) - Real.sqrt (m ^ 2 + 24)) / 6 > -9 / 5 := by
    linarith [h2.left]

  have h4 : (- (m : ℝ) + Real.sqrt (m ^ 2 + 24)) / 6 < 3 / 7 := by
    linarith [h1.right]

  have h5 : (m : ℝ) < 193 / 45 := by
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 24 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (m ^ 2 + 24 : ℝ) by nlinarith)]

  have h6 : (m : ℝ) > 71 / 21 := by
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 24 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (m ^ 2 + 24 : ℝ) by nlinarith)]

  have h7 : m < 5 := by
    by_contra h7
    push_neg at h7
    have h8 : m ≥ 5 := by omega
    have h9 : (m : ℝ) ≥ (5 : ℝ) := by exact_mod_cast h8
    nlinarith

  have h8 : m > 3 := by
    by_contra h8
    push_neg at h8
    have h9 : m ≤ 3 := by omega
    have h10 : (m : ℝ) ≤ (3 : ℝ) := by exact_mod_cast h9
    nlinarith

  omega