import Mathlib
open Real Set

theorem algebra_9142 : image (λ x => logb 2 (-x^2 + 2 * x + 7)) {x | -x^2 + 2 * x + 7 > 0} = {y | y ≤ 3} := by
  ext y
  simp only [mem_image, mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First, show that if y in image, then y ≤ 3
    rintro ⟨x, hx, rfl⟩
    have h1 : -x^2 + 2 * x + 7 > 0 := hx
    have h2 : logb 2 (-x^2 + 2 * x + 7) ≤ 3 := by
      have h3 : logb 2 (-x^2 + 2 * x + 7) ≤ logb 2 8 := by
        apply logb_le_logb_of_le
        all_goals nlinarith [sq_nonneg (x - 1)]
      have h4 : logb 2 8 = 3 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      linarith [h3, h4]
    linarith
  · -- Now, show that given y ≤ 3, there is some x in domain with log = y
    intro hy
    have h3 : y ≤ 3 := by linarith
    have h4 : (2 : ℝ) ^ y ≤ (2 : ℝ) ^ (3 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le
      all_goals linarith
    have h5 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      norm_num
    have h6 : (8 : ℝ) - (2 : ℝ) ^ y ≥ 0 := by
      have h7 : (2 : ℝ) ^ (y : ℝ) ≤ (8 : ℝ) := by
        have h8 : (2 : ℝ) ^ (y : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le
          all_goals linarith
        rw [h5] at h8
        linarith
      linarith
    use 1 + Real.sqrt (8 - (2 : ℝ) ^ y)
    constructor
    · -- Show that - (1 + Real.sqrt (8 - (2 : ℝ) ^ y))^2 + 2 * (1 + Real.sqrt (8 - (2 : ℝ) ^ y)) + 7 > 0
      have h7 : - (1 + Real.sqrt (8 - (2 : ℝ) ^ y))^2 + 2 * (1 + Real.sqrt (8 - (2 : ℝ) ^ y)) + 7 > 0 := by
        have h8 : (Real.sqrt (8 - (2 : ℝ) ^ y)) ^ 2 = 8 - (2 : ℝ) ^ y := Real.sq_sqrt (by linarith)
        have h9 : - (1 + Real.sqrt (8 - (2 : ℝ) ^ y))^2 + 2 * (1 + Real.sqrt (8 - (2 : ℝ) ^ y)) + 7 = (2 : ℝ) ^ y := by
          nlinarith [Real.sqrt_nonneg (8 - (2 : ℝ) ^ y), h8]
        have h10 : (2 : ℝ) ^ y > (0 : ℝ) := by
          positivity
        nlinarith [h9, h10]
      linarith [h7]
    · -- Show that log_2 (-x^2 + 2 * x + 7) = y
      have h7 : - (1 + Real.sqrt (8 - (2 : ℝ) ^ y))^2 + 2 * (1 + Real.sqrt (8 - (2 : ℝ) ^ y)) + 7 = (2 : ℝ) ^ y := by
        have h8 : (Real.sqrt (8 - (2 : ℝ) ^ y)) ^ 2 = 8 - (2 : ℝ) ^ y := Real.sq_sqrt (by linarith)
        nlinarith [Real.sqrt_nonneg (8 - (2 : ℝ) ^ y), h8]
      have h8 : logb 2 (- (1 + Real.sqrt (8 - (2 : ℝ) ^ y))^2 + 2 * (1 + Real.sqrt (8 - (2 : ℝ) ^ y)) + 7) = y := by
        rw [show - (1 + Real.sqrt (8 - (2 : ℝ) ^ y))^2 + 2 * (1 + Real.sqrt (8 - (2 : ℝ) ^ y)) + 7 = (2 : ℝ) ^ y by linarith [h7]]
        have h9 : logb 2 ((2 : ℝ) ^ y) = y := by
          rw [logb_rpow]
          all_goals linarith
        rw [h9]
      linarith [h8]