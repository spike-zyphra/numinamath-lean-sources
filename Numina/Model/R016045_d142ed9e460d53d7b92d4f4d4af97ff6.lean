import Mathlib

theorem algebra_213090 (x : ℝ) (hx : x^2 + x + 3 ≥ 0 ∧ x^2 - 2 * x + 4 ≥ 0) :
    Real.sqrt (x^2 + x + 3) - Real.sqrt (x^2 - 2 * x + 4) = 1 ↔ x = 2 := by
  constructor
  · -- Assume $\sqrt{x^{2}+x+3}-\sqrt{x^{2}-2x+4}=1$, prove $x = 2$.
    intro h
    have h1 : Real.sqrt (x^2 + x + 3) = 1 + Real.sqrt (x^2 - 2 * x + 4) := by
      linarith

    have h2 : Real.sqrt (x^2 + x + 3) ^ 2 = (1 + Real.sqrt (x^2 - 2 * x + 4)) ^ 2 := by
      rw [h1]

    have h3 : Real.sqrt (x^2 + x + 3) ^ 2 = x^2 + x + 3 := by
      exact Real.sq_sqrt (show x^2 + x + 3 ≥ 0 by linarith [hx.1])

    have h4 : (1 + Real.sqrt (x^2 - 2 * x + 4)) ^ 2 = 1 + 2 * Real.sqrt (x^2 - 2 * x + 4) + Real.sqrt (x^2 - 2 * x + 4) ^ 2 := by
      ring
    rw [h3, h4] at h2

    have h5 : Real.sqrt (x^2 - 2 * x + 4) ^ 2 = x^2 - 2 * x + 4 := by
      exact Real.sq_sqrt (show x^2 - 2 * x + 4 ≥ 0 by linarith [hx.2])
    rw [h5] at h2
    have h6 : 2 * Real.sqrt (x^2 - 2 * x + 4) = 3 * x - 2 := by
      nlinarith

    have h7 : Real.sqrt (x^2 - 2 * x + 4) ^ 2 = ((3 * x - 2) / 2) ^ 2 := by 
      nlinarith [h6]

    have h8 : Real.sqrt (x^2 - 2 * x + 4) ^ 2 = x^2 - 2 * x + 4 := by 
      exact Real.sq_sqrt (show x^2 - 2 * x + 4 ≥ 0 by linarith [hx.2])
    rw [h8] at h7

    have h9 : (3 * x - 2) ^ 2 = 4 * (x^2 - 2 * x + 4) := by
      nlinarith [h7]

    have h10 : (3 * x - 2) ^ 2 = 9 * x ^ 2 - 12 * x + 4 := by ring
    have h11 : 4 * (x^2 - 2 * x + 4) = 4 * x^2 - 8 * x + 16 := by ring
    rw [h10, h11] at h9

    have h12 : 5 * x^2 - 4 * x - 12 = 0 := by
      nlinarith [h9]

    have h13 : (x - 2) * (5 * x + 6) = 0 := by 
      linarith 

    cases' (mul_eq_zero.mp h13) with h14 h15
    · -- Case where x = 2.
      linarith
    · -- Case where x = -6/5.
      have h16 : x = -6 / 5 := by linarith
      rw [h16] at h
      have h21 : Real.sqrt ((-6 / 5) ^ 2 + (-6 / 5) + 3) = 9 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h22 : Real.sqrt ((-6 / 5) ^ 2 - 2 * (-6 / 5) + 4) = 14 / 5 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h21, h22] at h
      norm_num at h

  · -- Assume x = 2, prove $\sqrt{x^{2}+x+3}-\sqrt{x^{2}-2x+4}=1$.
    intro h
    rw [h]
    have h1 : Real.sqrt (2 ^ 2 + 2 + 3) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (2 ^ 2 - 2 * 2 + 4) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num