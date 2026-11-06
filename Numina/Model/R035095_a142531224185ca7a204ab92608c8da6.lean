import Mathlib

theorem algebra_8006 {m : ℝ} (hm : 0 ≤ m - 1) (h : √(m - 2 * √(m - 1)) + √(m + 2 * √(m - 1)) = m - 1) :
    m = 5 := by
  have h1 : 0 ≤ m - 1 := hm
  have h2 : (√(m - 1) - 1 : ℝ) ^ 2 = m - 2 * √(m - 1) := by
    nlinarith [Real.sqrt_nonneg (m - 1), Real.sq_sqrt (show (0 : ℝ) ≤ m - 1 by linarith)]
  have h3 : (√(m - 1) + 1 : ℝ) ^ 2 = m + 2 * √(m - 1) := by
    nlinarith [Real.sqrt_nonneg (m - 1), Real.sq_sqrt (show (0 : ℝ) ≤ m - 1 by linarith)]
  have h4 : √(m - 2 * √(m - 1)) = |√(m - 1) - 1| := by
    have h5 : m - 2 * √(m - 1) = (√(m - 1) - 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (m - 1), Real.sq_sqrt (show (0 : ℝ) ≤ m - 1 by linarith)]
    rw [h5]
    have h6 : √((√(m - 1) - 1) ^ 2) = |√(m - 1) - 1| := by
      rw [Real.sqrt_sq_eq_abs]
    exact h6
  have h7 : √(m + 2 * √(m - 1)) = √(m - 1) + 1 := by
    have h8 : m + 2 * √(m - 1) = (√(m - 1) + 1) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (m - 1), Real.sq_sqrt (show (0 : ℝ) ≤ m - 1 by linarith)]
    rw [h8]
    have h9 : √((√(m - 1) + 1) ^ 2) = √(m - 1) + 1 := by
      rw [Real.sqrt_sq (show 0 ≤ √(m - 1) + 1 by positivity)]
    exact h9
  rw [h4, h7] at h
  by_cases h8 : √(m - 1) - 1 ≥ 0
  · -- When √(m - 1) - 1 ≥ 0, we have |√(m - 1) - 1| = √(m - 1) - 1
    have h9 : |√(m - 1) - 1| = √(m - 1) - 1 := by
      rw [abs_of_nonneg h8]
    rw [h9] at h
    have h10 : 2 * √(m - 1) = m - 1 := by
      nlinarith [h, Real.sqrt_nonneg (m - 1)]
    have h11 : (√(m - 1) : ℝ) ^ 2 = m - 1 := by
      rw [Real.sq_sqrt]
      linarith
    have h12 : (m - 1 : ℝ) * (m - 1 - 4) = 0 := by
      nlinarith [sq_nonneg (√(m - 1) - 2), h10, Real.sqrt_nonneg (m - 1), h11]
    cases' (mul_eq_zero.mp h12) with h15 h16
    · -- m - 1 = 0
      have h17 : m - 1 = 0 := by
        nlinarith
      have h18 : √(m - 1) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals linarith
      nlinarith [show √(m - 1) - 1 ≥ 0 by linarith, h18]
    · -- m - 1 - 4 = 0
      linarith
  · -- When √(m - 1) - 1 < 0, we have |√(m - 1) - 1| = 1 - √(m - 1)
    have h9 : |√(m - 1) - 1| = 1 - √(m - 1) := by
      rw [abs_of_neg (show (√(m - 1) - 1) < 0 by nlinarith)]
      all_goals nlinarith [Real.sqrt_nonneg (m - 1)]
    rw [h9] at h
    -- Let's analyze the equation: 1 - √(m-1) + √(m-1) + 1 = m - 1 => 2 = m - 1 => m = 3
    -- But from hypothesis: √(m-1) < 1 => m-1 < 1 => m < 2
    -- Contradicts with m = 3
    -- Therefore impossible
    nlinarith [h, Real.sqrt_nonneg (m - 1), Real.sq_sqrt (show (0 : ℝ) ≤ m - 1 by linarith)]