import Mathlib

theorem algebra_246601 (x : ℝ) :
    Real.sqrt (x ^ 2 + 9) + Real.sqrt (x ^ 2 - 6 * x + 10) = 5 ↔
    x = 9 / 4 := by
  constructor
  · -- Let's prove that if the equation holds, then x = 9/4.
    intro h
    have h1 : 0 ≤ Real.sqrt (x ^ 2 + 9) := Real.sqrt_nonneg (x ^ 2 + 9)
    have h2 : 0 ≤ Real.sqrt (x ^ 2 - 6 * x + 10) := Real.sqrt_nonneg (x ^ 2 - 6 * x + 10)
    have h3 : x ^ 2 - 6 * x + 10 ≥ 0 := by
      nlinarith [sq_nonneg (x - 3)]
    have h4 : (Real.sqrt (x ^ 2 + 9) + Real.sqrt (x ^ 2 - 6 * x + 10)) ^ 2 = 25 := by 
      rw [h]
      norm_num
    have h5 : (Real.sqrt (x ^ 2 + 9) + Real.sqrt (x ^ 2 - 6 * x + 10)) ^ 2 =
        (Real.sqrt (x ^ 2 + 9)) ^ 2 + (Real.sqrt (x ^ 2 - 6 * x + 10)) ^ 2 + 2 * (Real.sqrt (x ^ 2 + 9) * Real.sqrt (x ^ 2 - 6 * x + 10)) := by ring
    have h6 : (Real.sqrt (x ^ 2 + 9)) ^ 2 = x^2 + 9 := by 
      rw [Real.sq_sqrt]
      nlinarith
    have h7 : (Real.sqrt (x ^ 2 - 6 * x + 10)) ^ 2 = x^2 - 6 * x + 10 := by
      rw [Real.sq_sqrt]
      nlinarith [h3]
    rw [h5, h6, h7] at h4
    -- From h4, we can compute to get:
    -- (x^2+9) + (x^2-6x+10) = 2x^2 -6x +19.
    -- So 2x^2 -6 x +19 + 2 \cdot \sqrt{A \cdot B} = 25.
    -- Then 2 \cdot \sqrt{A \cdot B} = (6 - 6x + 6).
    have h8 : Real.sqrt (x ^ 2 + 9) * Real.sqrt (x ^ 2 - 6 * x + 10) = 3 + 3 * x - x ^ 2 := by
      nlinarith [h4]
    have h9 : Real.sqrt (x ^ 2 + 9) * Real.sqrt (x ^ 2 - 6 * x + 10) = Real.sqrt ((x ^ 2 + 9) * (x ^ 2 - 6 * x + 10)) := by
      rw [← Real.sqrt_mul (by nlinarith)]
    rw [h9] at h8
    have h10 : (x ^ 2 + 9) * (x ^ 2 - 6 * x + 10) = (3 + 3 * x - x ^ 2) ^ 2 := by
      calc
        (x ^ 2 + 9) * (x ^ 2 - 6 * x + 10) = (Real.sqrt ((x ^ 2 + 9) * (x ^ 2 - 6 * x + 10))) ^ 2 := by 
          rw [Real.sq_sqrt]
          nlinarith [show (x ^ 2 + 9) * (x ^ 2 - 6 * x + 10) ≥ 0 by nlinarith [sq_nonneg (x - 3), sq_nonneg (x ^ 2 +9), sq_nonneg (x ^ 2 - 6 * x + 10)]]
        _ = (3 + 3 * x - x ^ 2) ^ 2 := by
          rw [h8]
        _ = (3 + 3 * x - x ^ 2) ^ 2 := by ring
    ring_nf at h10 
    have h11 : (x - 9 / 4) ^ 2 = 0 := by
      nlinarith
    have h12 : x - 9 / 4 = 0 := by
      apply pow_eq_zero 
      exact h11
    linarith
  · -- Let's prove the reverse direction: x = 9/4 implies the equation.
    intro h
    rw [h]
    have h1 : Real.sqrt ((9 / 4 : ℝ) ^ 2 + 9) = 15 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith
      <;> norm_num
    have h2 : Real.sqrt ((9 / 4 : ℝ) ^ 2 - 6 * (9 / 4 : ℝ) + 10) = 5 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith
      <;> norm_num
    rw [h1, h2]
    all_goals norm_num
    all_goals linarith