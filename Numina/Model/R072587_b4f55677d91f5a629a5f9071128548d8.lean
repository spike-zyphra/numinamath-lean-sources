import Mathlib

theorem algebra_187997 (x : ℝ) :
    x^4 + 2 * x^3 - 11 * x^2 + 4 * x + 4 = 0 ↔ x = 1 ∨ x = 2 ∨ x = (-5 - √17) / 2 ∨ x = (-5 + √17) / 2 := by
  constructor
  · -- (→) If polynomial equals zero, then one of the roots equals zero
    intro h
    have h1 : x^4 + 2 * x^3 - 11 * x^2 + 4 * x + 4 = (x^2 - 3 * x + 2) * (x^2 + 5 * x + 2) := by
      ring
    rw [h1] at h
    cases' (mul_eq_zero.1 h) with h2 h3
    · -- Case where first factor equals zero
      have h4 : x^2 - 3 * x + 2 = (x - 1) * (x - 2) := by
        ring
      rw [h4] at h2
      cases' (mul_eq_zero.1 h2) with h5 h6
      · -- Case where (x - 1) equals zero
        left
        linarith
      · -- Case where (x - 2) equals zero
        right
        left
        linarith
    · -- Case where second factor equals zero
      have h4 : x^2 + 5 * x + 2 = (x - (-5 - Real.sqrt 17) / 2) * (x - (-5 + Real.sqrt 17) / 2) := by
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        linarith
      rw [h4] at h3
      cases' (mul_eq_zero.1 h3) with h7 h8
      · -- Case where first factor equals zero
        right
        right
        left
        linarith
      · -- Case where second factor equals zero
        right
        right
        right
        linarith
  · -- (←) If one of the roots equals zero, then the polynomial equals zero
    rintro (h | h | h | h)
    · -- First root
      rw [h]
      norm_num
    · -- Second root
      rw [h]
      norm_num
    · -- Third root
      rw [h]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num : (17 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num : (17 : ℝ) > 0)]
    · -- Fourth root
      rw [h]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num : (17 : ℝ) ≥ 0), Real.sqrt_pos.mpr (show (0 : ℝ) < 17 by norm_num : (17 : ℝ) > 0)]