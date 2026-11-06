import Mathlib

theorem algebra_300657 {x : ℝ} (hx : x^2 + 5 * x - 2 ≥ 0) (hx' : x^2 + 5 * x - 5 ≥ 0)
    (h : Real.sqrt (x^2 + 5 * x - 2) - Real.sqrt (x^2 + 5 * x - 5) = 1) :
    x = 1 ∨ x = -6 := by
  have h1 : Real.sqrt (x^2 + 5 * x - 2) = 1 + Real.sqrt (x^2 + 5 * x - 5) := by
    linarith
  have h2 : Real.sqrt (x^2 + 5 * x - 2) ^ 2 = (1 + Real.sqrt (x^2 + 5 * x - 5)) ^ 2 := by
    rw [h1]
  have h3 : Real.sqrt (x^2 + 5 * x - 2) ^ 2 = x^2 + 5 * x - 2 := by
    exact Real.sq_sqrt hx
  have h4 : (1 + Real.sqrt (x^2 + 5 * x - 5)) ^ 2 = 1 + 2 * Real.sqrt (x^2 + 5 * x - 5) + (Real.sqrt (x^2 + 5 * x - 5) ^ 2) := by
    ring
  have h5 : Real.sqrt (x^2 + 5 * x - 5) ^ 2 = x^2 + 5 * x - 5 := by
    exact Real.sq_sqrt hx'
  rw [h3, h4, h5] at h2
  have h6 : Real.sqrt (x^2 + 5 * x - 5) = 1 := by
    nlinarith [Real.sqrt_nonneg (x^2 + 5 * x - 5)]
  have h7 : x^2 + 5 * x - 5 = 1 := by
    calc
      x^2 + 5 * x - 5 = Real.sqrt (x^2 + 5 * x - 5) ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      _ = 1 ^ 2 := by
        rw [h6]
      _ = (1 : ℝ) := by
        norm_num
  have h8 : x^2 + 5 * x - 6 = 0 := by
    nlinarith
  have h9 : (x - 1) * (x + 6) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- First case where x - 1 = 0, so x = 1.
    left
    linarith
  · -- Second case where x + 6 = 0, so x = -6.
    right
    linarith