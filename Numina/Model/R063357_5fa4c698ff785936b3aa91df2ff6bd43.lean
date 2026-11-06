import Mathlib

theorem algebra_298229 (x : ℝ) (h : 0 ≤ x^2 + 4 * x + 8 ∧ 0 ≤ x^2 - 8 * x + 20) :
    Real.sqrt (x^2 + 4 * x + 8) + Real.sqrt (x^2 - 8 * x + 20) = 10 ↔
    x = 1 + 5 * Real.sqrt 3 / 2 ∨ x = 1 - 5 * Real.sqrt 3 / 2 := by
  constructor
  · -- Forward implication: if the equation holds, then the solutions are as given
    intro h_eq
    have h1 : 0 ≤ x^2 + 4 * x + 8 := h.1
    have h2 : 0 ≤ x^2 - 8 * x + 20 := h.2
    set a := Real.sqrt (x^2 + 4 * x + 8) with ha
    set b := Real.sqrt (x^2 - 8 * x + 20) with hb
    have h_eq2 : a + b = 10 := by
      linarith [h_eq, ha, hb]
    have ha2 : a^2 = x^2 + 4 * x + 8 := by
      rw [Real.sq_sqrt]
      linarith
    have hb2 : b^2 = x^2 - 8 * x + 20 := by
      rw [Real.sq_sqrt]
      linarith
    have h3 : a^2 - b^2 = 12 * (x - 1) := by
      nlinarith
    have h4 : b = 10 - a := by
      linarith
    rw [h4] at h3
    have h5 : a = (3 * x + 22) / 5 := by
      nlinarith
    have h6 : a^2 = ((3 * x + 22) / 5)^2 := by
      rw [h5]
    rw [ha2] at h6
    have h7 : (4 : ℝ) * x^2 - 8 * x - 71 = 0 := by
      nlinarith [h6]
    have h8 : (x - (1 + 5 * Real.sqrt 3 / 2)) * (x - (1 - 5 * Real.sqrt 3 / 2)) = 0 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), h7]
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- First case
      left
      linarith
    · -- Second case
      right
      linarith
  · -- Reverse implication: if x equals either of the two solutions, then the equation holds
    rintro (h | h)
    · -- First solution
      have hx : x = 1 + 5 * Real.sqrt 3 / 2 := by linarith
      have h1 : Real.sqrt (x^2 + 4 * x + 8) = 5 + (3 * Real.sqrt 3 / 2) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), hx, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      have h2 : Real.sqrt (x^2 - 8 * x + 20) = 5 - (3 * Real.sqrt 3 / 2) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), hx, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      rw [h1, h2]
      nlinarith
    · -- Second solution
      have hx : x = 1 - 5 * Real.sqrt 3 / 2 := by linarith
      have h1 : Real.sqrt (x^2 + 4 * x + 8) = 5 - (3 * Real.sqrt 3 / 2) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), hx, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      have h2 : Real.sqrt (x^2 - 8 * x + 20) = 5 + (3 * Real.sqrt 3 / 2) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), hx, Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)]
      rw [h1, h2]
      nlinarith