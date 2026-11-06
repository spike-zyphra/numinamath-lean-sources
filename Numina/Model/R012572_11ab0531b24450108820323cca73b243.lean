import Mathlib

theorem algebra_212715 (x : ℝ) : x^6 - 2020 * x^2 - Real.sqrt 2021 = 0 ↔ x^4 = 2021 := by
  constructor
  · -- Assume x^6 - 2020 * x^2 - Real.sqrt 2021 = 0, prove x^4 = 2021.
    intro h
    have h1 : (x^2 - Real.sqrt 2021) * ( (x^2)^2 + Real.sqrt 2021 * (x^2) + 1 ) = 0 := by
      nlinarith [Real.sqrt_nonneg 2021, Real.sq_sqrt (show (2021 : ℝ) ≥ 0 by norm_num), sq_nonneg (x^2 - Real.sqrt 2021), sq_nonneg (x), sq_nonneg (x^2), sq_nonneg ( (x^2)^2 - (2021 : ℝ) * (x^2) + (2021 : ℝ) ), sq_nonneg (x^2 - Real.sqrt 2021), h]
    have h2 : x^2 - Real.sqrt 2021 = 0 ∨ ( (x^2)^2 + Real.sqrt 2021 * (x^2) + 1 ) = 0 := by
      cases (mul_eq_zero.1 h1) with 
      | inl h3 => 
        left 
        linarith
      | inr h4 => 
        right 
        linarith
    cases h2 with
    | inl h3 =>
      have h4 : x^2 = Real.sqrt 2021 := by linarith
      have h5 : x^4 = 2021 := by
        calc 
          x^4 = (x^2)^2 := by ring
          _ = (Real.sqrt 2021)^2 := by rw [h4]
          _ = (2021 : ℝ) := Real.sq_sqrt (by norm_num)
      assumption
    | inr h4 =>
      nlinarith [sq_nonneg (x^2 + Real.sqrt 2021 / 2), sq_nonneg (x), Real.sqrt_nonneg 2021, Real.sq_sqrt (show (2021 : ℝ) ≥ 0 by norm_num), sq_nonneg (x^2 - Real.sqrt 2021 / 2)]
  · -- Show x^4 = 2021 implies x^6 - 2020 * x^2 - Real.sqrt 2021 = 0.
    intro h
    have h5 : x^4 = 2021 := h
    have h6 : x^6 = x^2 * x^4 := by ring
    rw [h6, h5]
    have h7 : (x^2) * (2021 : ℝ) = 2020 * x^2 + Real.sqrt 2021 := by
      have h8 : (x^2) * (2021 : ℝ) - 2020 * x^2 - Real.sqrt 2021 = 0 := by
        nlinarith [sq_nonneg (x^2 - Real.sqrt 2021), Real.sqrt_nonneg 2021, Real.sq_sqrt (show (2021 : ℝ) ≥ 0 by norm_num), sq_nonneg (x), h5]
      linarith
    linarith