import Mathlib

theorem algebra_186992 (x : ℝ) (hx : 2*x^2-8*x+12 ≥ 0) :
    x^2 - 4*x - 6 = Real.sqrt (2*x^2 - 8*x + 12) ↔ x = -2 ∨ x = 6 := by
  constructor
  · -- First, we prove the forward direction: if the equation holds, then x is either -2 or 6.
    intro h
    have h1 : (x^2 - 4*x - 6) ^ 2 = (Real.sqrt (2 * x ^ 2 - 8 * x + 12)) ^ 2 := by
      rw [h]
    have h2 : (Real.sqrt (2 * x ^ 2 - 8 * x + 12)) ^ 2 = 2 * x ^ 2 - 8 * x + 12 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h2] at h1
    have h3 : (x + 2) * (x - 6) * (x^2 - 4*x - 2) = 0 := by
      nlinarith [sq_nonneg (x^2 - 4*x - 6 - (2*x - 4)), sq_nonneg (x + 2), sq_nonneg (x - 6)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    cases' (mul_eq_zero.1 h4) with h6 h7
    · -- Case x + 2 = 0, so x = -2
      left
      linarith
    · -- Case x - 6 = 0, so x = 6
      right
      linarith
    · -- Case x^2 - 4x - 2 = 0
      have h8 : x^2 - 4*x - 2 = 0 := by
        nlinarith
      -- Show that in this case the equation doesn't hold
      nlinarith [Real.sqrt_nonneg (2 * x ^ 2 - 8 * x + 12), sq_nonneg (x^2 - 4*x - 6 - Real.sqrt (2*x^2 - 8*x + 12)), sq_nonneg (x^2 - 4*x - 6 - (x^2 - 4*x - 6)), Real.sq_sqrt (show 0 ≤ (2 * x^2 - 8 * x + 12) by linarith)]
  · -- Now the reverse direction: if x is either -2 or 6, then the equation holds.
    rintro (h | h)
    · -- Case x = -2
      rw [h]
      have h2 : 2 * (-2:ℝ) ^ 2 - 8 * (-2:ℝ) + 12 = (36:ℝ) := by norm_num
      have h3 : Real.sqrt (2 * (-2:ℝ) ^ 2 - 8 * (-2:ℝ) + 12) = 6 := by
        rw [h2]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      have h4 : (-2:ℝ) ^ 2 - 4 * (-2:ℝ) - 6 = (6:ℝ) := by norm_num
      rw [h3]
      linarith [h4]
    · -- Case x = 6
      rw [h]
      have h2 : 2 * (6:ℝ) ^ 2 - 8 * (6:ℝ) + 12 = (36:ℝ) := by norm_num
      have h3 : Real.sqrt (2 * (6:ℝ) ^ 2 - 8 * (6:ℝ) + 12) = 6 := by
        rw [h2]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> nlinarith
      have h4 : (6:ℝ) ^ 2 - 4 * (6:ℝ) - 6 = (6:ℝ) := by norm_num
      rw [h3]
      linarith [h4]