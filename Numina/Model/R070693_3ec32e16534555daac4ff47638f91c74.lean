import Mathlib

theorem algebra_8883 (x : ℝ) (hx : x ^ 2 - 4 * x + 13 ≥ 0) : Real.sqrt (x ^ 2 - 4 * x + 13) + 1 = 2 * x ↔ x = 2 := by
  constructor
  · -- Forward direction: if $\sqrt{x^2 - 4x + 13} + 1 = 2x$, then $x = 2$
    intro h
    have h1 : Real.sqrt (x ^ 2 - 4 * x + 13) = 2 * x - 1 := by linarith
    have h2 : Real.sqrt (x ^ 2 - 4 * x + 13) ≥ 0 := by positivity
    have h3 : (2 * x - 1) ≥ 0 := by linarith [h1, h2]
    have h4 : (Real.sqrt (x ^ 2 - 4 * x + 13)) ^ 2 = (2 * x - 1) ^ 2 := by
      rw [h1]
    have h5 : (Real.sqrt (x ^ 2 - 4 * x + 13)) ^ 2 = x ^ 2 - 4 * x + 13 := Real.sq_sqrt (by linarith)
    rw [h5] at h4
    have h6 : (2 * x - 1) ^ 2 = 4 * x^2 - 4 * x + 1 := by ring
    rw [h6] at h4
    have h7 : 3 * x^2 = 12 := by linarith
    have h8 : x^2 = 4 := by linarith
    have h9 : x = 2 ∨ x = -2 := by
      have h10 : x^2 - 4 = 0 := by
        nlinarith
      have h11 : (x - 2) * (x + 2) = 0 := by
        linarith
      cases (mul_eq_zero.mp h11) with
      | inl h12 =>
        left
        linarith
      | inr h13 =>
        right
        linarith
    cases h9 with
    | inl h2 =>
      exact h2
    | inr h2 =>
      nlinarith
  · -- Backward direction: if x = 2, then $\sqrt{x^2 - 4 x + 13} + 1 = 2 x$
    intro h
    rw [h]
    have h1 : Real.sqrt ((2 : ℝ) ^ 2 - 4 * (2 : ℝ) + 13) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    all_goals norm_num