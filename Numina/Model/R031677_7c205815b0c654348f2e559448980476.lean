import Mathlib

theorem algebra_9822 {x : ℝ} (hx : x > 0) : x = Real.sqrt x + 506 ↔ x = 529 := by
  constructor
  · -- Assume x = sqrt x + 506, prove x = 529
    intro h
    have h1 : Real.sqrt x ≥ 0 := by
      apply Real.sqrt_nonneg
    have h2 : x - 506 = Real.sqrt x := by
      nlinarith
    have h3 : (x - 506) ^ 2 = (Real.sqrt x) ^ 2 := by
      rw [h2]
    have h4 : (Real.sqrt x) ^ 2 = x := by
      rw [Real.sq_sqrt]
      linarith
    rw [h4] at h3
    have h5 : (x) ^ 2 - 1013 * (x) + 506 ^ 2 = 0 := by
      nlinarith
    have h6 : (x - 529) * (x - 484) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case x - 529 = 0
      linarith
    · -- Case x - 484 = 0
      have h9 : x = 484 := by
        linarith
      rw [h9] at h
      have h10 : Real.sqrt (484 : ℝ) = (22 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h10] at h
      all_goals linarith
  · -- Assume x = 529, prove x = sqrt x + 506
    intro h
    rw [h]
    have h11 : Real.sqrt (529 : ℝ) = (23 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h11]
    all_goals norm_num