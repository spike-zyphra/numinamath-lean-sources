import Mathlib

theorem algebra_252206 (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt (x + 7) * Real.sqrt (3 * x - 2) = 3 * Real.sqrt (x - 1) * Real.sqrt (x + 2) ↔ x = 2 := by
  constructor
  · -- Forward direction: equation implies x = 2
    intro h
    have h1 : x + 7 ≥ 0 := by linarith
    have h2 : 3 * x - 2 ≥ 0 := by nlinarith
    have h3 : x - 1 ≥ 0 := by linarith
    have h4 : x + 2 ≥ 0 := by linarith

    have h5 : (Real.sqrt (x + 7) * Real.sqrt (3 * x - 2)) ^ 2 = (3 * Real.sqrt (x - 1) * Real.sqrt (x + 2)) ^ 2 := by
      rw [h]

    have h6 : (Real.sqrt (x + 7) * Real.sqrt (3 * x - 2)) ^ 2 = (Real.sqrt (x + 7)) ^ 2 * (Real.sqrt (3 * x - 2)) ^ 2 := by ring
    have h7 : (Real.sqrt (x + 7)) ^ 2 = x + 7 := Real.sq_sqrt (show 0 ≤ (x + 7 : ℝ) by linarith)
    have h8 : (Real.sqrt (3 * x - 2)) ^ 2 = 3 * x - 2 := Real.sq_sqrt (show 0 ≤ (3 * x - 2 : ℝ) by nlinarith)

    have h9 : (3 * Real.sqrt (x - 1) * Real.sqrt (x + 2)) ^ 2 = 9 * ((Real.sqrt (x - 1)) ^ 2 * (Real.sqrt (x + 2)) ^ 2) := by
      ring_nf

    have h10 : (Real.sqrt (x - 1)) ^ 2 = x - 1 := Real.sq_sqrt (show 0 ≤ (x - 1 : ℝ) by linarith)
    have h11 : (Real.sqrt (x + 2)) ^ 2 = x + 2 := Real.sq_sqrt (show 0 ≤ (x + 2 : ℝ) by linarith)

    rw [h6, h7, h8] at h5
    rw [h9, h10, h11] at h5

    have h12 : 3 * x^2 + 19 * x - 14 = 9 * x^2 + 9 * x - 18 := by
      nlinarith

    have h13 : 6 * x^2 - 10 * x - 4 = 0 := by 
      nlinarith

    have h14 : 3 * x^2 - 5 * x - 2 = 0 := by
      nlinarith

    have h15 : 3 * x^2 - 5 * x - 2 = (x - 2) * (3 * x + 1) := by
      ring

    rw [h15] at h14

    cases' (mul_eq_zero.1 h14) with h16 h17
    · -- Case x - 2 = 0, so x = 2
      linarith

    · -- Case 3x + 1 = 0, so x = -1/3
      nlinarith

  · -- Backward direction: x = 2 implies the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (2 + 7 : ℝ) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

    have h2 : Real.sqrt (3 * (2 : ℝ) - 2) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

    have h3 : Real.sqrt (2 - 1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

    have h4 : Real.sqrt (2 + 2 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num

    rw [h1, h2, h3, h4]
    all_goals norm_num