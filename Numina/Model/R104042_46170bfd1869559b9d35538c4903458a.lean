import Mathlib

theorem algebra_206806 {x : ℝ} (hx : x^2 - 1 ≥ 0) :
    (x^2 + x)^2 + Real.sqrt (x^2 - 1) = 0 ↔ x = -1 := by
  constructor
  · -- Assume (x^2 + x)^2 + Real.sqrt (x^2 - 1) = 0, prove x = -1
    intro h
    have h1 : (x ^ 2 + x) ^ 2 ≥ 0 := by
      positivity
    have h2 : Real.sqrt (x ^ 2 - 1) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h3 : (x ^ 2 + x) ^ 2 = 0 := by
      linarith [h1, h2, h]
    have h4 : Real.sqrt (x ^ 2 - 1) = 0 := by
      linarith [h1, h2, h]
    have h5 : x ^ 2 + x = 0 := by
      nlinarith
    have h6 : x ^ 2 - 1 = 0 := by
      rw [Real.sqrt_eq_zero (by nlinarith)] at h4
      linarith
    have h5' : x = 0 ∨ x = -1 := by
      have : x * (x + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp this) with h7 h8
      · -- Case $x = 0$:
        left
        linarith
      · -- Case $x + 1 = 0$, so $x = -1$:
        right
        nlinarith
    cases h5' with
    | inl h7 =>
      exfalso
      rw [h7] at h6 hx
      all_goals
      nlinarith
    | inr h8 =>
      exact h8
  · -- Assume x = -1, prove (x^2 + x)^2 + Real.sqrt (x^2 - 1) = 0
    intro h
    rw [h]
    have h1 : ( (-1 : ℝ) ^ 2 + (-1 : ℝ ) ) ^ 2 + Real.sqrt ( (-1 : ℝ) ^ 2 - 1 ) = 0 := by
      norm_num
      all_goals
      norm_num [Real.sqrt_eq_iff_sq_eq]
    linarith [h1]