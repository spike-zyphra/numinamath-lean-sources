import Mathlib

theorem algebra_243331 (x : ℝ) :
    abs (x + 3) + 2 * Real.sqrt (x^2 + 2 * x + 1) = 7 ↔
    x = -4 ∨ x = 2 / 3 := by
  constructor
  · -- Assume abs (x + 3) + 2 * Real.sqrt (x^2 + 2 * x + 1) = 7 prove x = -4 ∨ x = 2 / 3
    intro h
    have h1 : Real.sqrt (x^2 + 2 * x + 1) = abs (x + 1) := by
      have h2 : x^2 + 2 * x + 1 = (x + 1) ^ 2 := by
        ring
      rw [h2]
      rw [Real.sqrt_sq_eq_abs]
    rw [h1] at h

    cases' abs_cases (x + 3) with h3 h3
    · -- Case where x + 3 ≥ 0, so |x + 3| = x + 3
      cases' abs_cases (x + 1) with h4 h4
      · -- Case where x + 1 ≥ 0, so |x + 1| = x + 1
        right
        linarith
      · -- Case where x + 1 < 0, so |x + 1| = -(x + 1)
        exfalso
        linarith
    · -- Case where x + 3 < 0, so |x + 3| = -(x + 3)
      cases' abs_cases (x + 1) with h4 h4
      · -- Case where x + 1 ≥ 0, so |x + 1| = x + 1
        exfalso
        linarith
      · -- Case where x + 1 < 0, so |x + 1| = -(x + 1)
        left
        linarith
  · -- Assume x = -4 ∨ x = 2 / 3 prove abs (x + 3) + 2 * Real.sqrt (x^2 + 2 * x + 1) = 7
    rintro (h | h)
    · -- Case x = -4
      rw [h]
      have h1 : Real.sqrt ((-4: ℝ) ^ 2 + 2 * (-4) + 1) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h1]
      norm_num [abs_of_nonneg]
    · -- Case x = 2 / 3
      rw [h]
      have h2 : Real.sqrt (( (2/3 : ℝ) ) ^ 2 + 2 * ( (2/3 : ℝ) ) + 1) = (5 / 3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h2]
      norm_num [abs_of_pos]