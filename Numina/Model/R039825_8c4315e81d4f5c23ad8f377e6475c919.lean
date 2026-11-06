import Mathlib
theorem algebra_314650 (x : ℝ) (hx : 2 * x ^ 2 - 15 * x + 1998 ≥ 0) :
    2 * x ^ 2 - 15 * x - Real.sqrt (2 * x ^ 2 - 15 * x + 1998) = -18 ↔
    x = -3 / 2 ∨ x = 9 := by
  constructor
  · -- Assume 2 * x ^ 2 - 15 * x - Real.sqrt (2 * x ^ 2 - 15 * x + 1998) = -18
    intro h
    have h1 : Real.sqrt (2 * x ^ 2 - 15 * x + 1998) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : 2 * x ^ 2 - 15 * x + 18 = Real.sqrt (2 * x ^ 2 - 15 * x + 1998) := by
      nlinarith
    have h3 : (2 * x ^ 2 - 15 * x + 18) ^ 2 = 2 * x ^ 2 - 15 * x + 1998 := by
      calc
        (2 * x ^ 2 - 15 * x + 18) ^ 2 = (Real.sqrt (2 * x ^ 2 - 15 * x + 1998)) ^ 2 := by
          rw [show Real.sqrt (2 * x ^ 2 - 15 * x + 1998) = 2 * x ^ 2 - 15 * x + 18 by linarith [h2]]
        _ = 2 * x ^ 2 - 15 * x + 1998 := by
          rw [Real.sq_sqrt]
          linarith
    have h4 : (x - 9) * (x + 3 / 2) = 0 := by
      nlinarith [sq_nonneg (2 * x ^ 2 - 15 * x - 9), sq_nonneg (x + 3 / 2), sq_nonneg (x - 9), sq_nonneg (2 * x ^ 2 - 15 * x - 27)]
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- x - 9 = 0
      right
      linarith
    · -- x + 3 / 2 = 0
      left
      linarith
  · -- Assume x = -3/2 ∨ x = 9
    rintro (h | h)
    · -- x = -3/2
      have hx1 : x = -3 / 2 := by linarith
      have h6 : Real.sqrt (2 * x ^ 2 - 15 * x + 1998) = 45 := by
        rw [hx1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h6]
      nlinarith
    · -- x = 9
      have hx1 : x = 9 := by linarith
      have h6 : Real.sqrt (2 * x ^ 2 - 15 * x + 1998) = 45 := by
        rw [hx1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h6]
      nlinarith