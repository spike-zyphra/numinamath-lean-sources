import Mathlib

theorem algebra_3391 (x : ℝ) (hx : 0 < x) : 3 * x ^ 2 - 5 * x - 1 = 0 ↔
    x = (5 + Real.sqrt 37) / 6 := by
  constructor
  · -- Assume 3 * x ^ 2 - 5 * x - 1 = 0 prove x = (5 + Real.sqrt 37) / 6
    intro h
    have h1 : 3 * x ^ 2 - 5 * x - 1 = 0 := h
    have h2 : 3 * x ^ 2 - 5 * x - 1 = 3 * (x - (5 + Real.sqrt 37) / 6) * (x - (5 - Real.sqrt 37) / 6) := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (37 : ℝ) > 0), Real.sq_sqrt (show (37 : ℝ) ≥ 0 by norm_num)]
    rw [h2] at h1
    cases (mul_eq_zero.1 h1) with
    | inl h3 =>
      -- Case where $3 * (x - (5 + Real.sqrt 37) / 6) = 0$
      have h6 : x - (5 + Real.sqrt 37) / 6 = 0 := by
        linarith
      linarith
    | inr h4 =>
      -- Case where $x - (5 - Real.sqrt 37) / 6 = 0$
      have h7 : x = (5 - Real.sqrt 37) / 6 := by
        linarith
      have h8 : Real.sqrt 37 > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h9 : (5 - Real.sqrt 37 : ℝ) < 0 := by
        nlinarith [Real.sqrt_nonneg (37 : ℝ), Real.sq_sqrt (show (37 : ℝ) ≥ 0 by norm_num)]
      nlinarith [h7, h9, Real.sqrt_nonneg (37 : ℝ), Real.sq_sqrt (show (37 : ℝ) ≥ 0 by norm_num)]
  · -- Assume x = (5 + Real.sqrt 37) / 6 prove 3 * x ^ 2 - 5 * x - 1 = 0
    intro h
    rw [h]
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (37 : ℝ) > 0), Real.sq_sqrt (show (37 : ℝ) ≥ 0 by norm_num)]