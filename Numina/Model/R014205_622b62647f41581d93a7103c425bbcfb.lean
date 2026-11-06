import Mathlib

theorem algebra_99354 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h₁ : 4 / x ^ 4 - 2 / x ^ 2 = 3) (h₂ : y ^ 4 + y ^ 2 = 3) :
    4 / x ^ 4 + y ^ 4 = 7 := by
  have h3 : 4 / x ^ 4 = (2 / x ^ 2) ^ 2 := by
    field_simp
    <;> nlinarith
  have eq1 : (2 / x ^ 2) ^ 2 - (2 / x ^ 2) - 3 = 0 := by
    have eq2 : 4 / x ^ 4 - 2 / x ^ 2 = 3 := h₁
    have eq3 : 4 / x ^ 4 = (2 / x ^ 2) ^ 2 := h3
    rw [eq3] at eq2
    linarith
  have h4 : (2 / x ^ 2) > 0 := by
    have hx1 : x ^ 2 > 0 := by
      exact sq_pos_of_ne_zero hx
    positivity
  have h5 : (2 / x ^ 2) = (1 + Real.sqrt 13) / 2 := by
    have h5 : (2 / x ^ 2) ^ 2 - (2 / x ^ 2) - 3 = 0 := eq1
    have h44 : (2 / x ^ 2) > 0 := h4
    have : ( (2 / x ^ 2) - ( (1 + Real.sqrt 13) / 2 ) ) * ( (2 / x ^ 2) - ( (1 - Real.sqrt 13) / 2 ) ) = 0 := by 
      nlinarith [ Real.sqrt_nonneg 13, Real.sq_sqrt (show (13: ℝ) ≥ 0 by norm_num) ]
    cases' (mul_eq_zero.mp this) with h6 h7
    · linarith
    · -- The case where `5 - (3 + Real.sqrt 3) * x ≤ 0` implies `a ≤ 0` which contradicts `hc : 2 / (x ^2) > 0`
      nlinarith [ Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ (0 : ℝ) by norm_num) ]
  have eq3 : 4 / x ^ 4 = (7 + Real.sqrt 13)/2 := by
    have eq4 : 4 / x ^ 4 = (2 / x ^ 2) ^ 2 := h3
    rw [eq4]
    rw [h5]
    nlinarith [ Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ (0 : ℝ) by norm_num) ]
  -- Now solving the second equation.
  have eq4 : y^2 = ( -1 + Real.sqrt 13 ) / 2 := by
    have eq5 : y ^ 4 + y ^ 2 - 3 = 0 := by
      linarith [h₂]
    have eq6 : (y ^ 2) ^ 2 + (y ^ 2) - 3 = 0 := by
      nlinarith
    have h1 : y^2 ≥ 0 := by
      positivity
    have : (y ^ 2 - ( -1 + Real.sqrt 13 ) / 2 ) * (y ^ 2 - ( -1 - Real.sqrt 13 ) / 2 ) = 0 := by 
      nlinarith [ Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ (0 : ℝ) by norm_num) ]
    cases' (mul_eq_zero.mp this) with h6 h7
    · linarith
    · -- The case where `5 - (3 + Real.sqrt 3) * x ≤ 0` implies `a ≤ 0` which contradicts `hc : 2 / (x ^2) > 0`
      nlinarith [ Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ (0 : ℝ) by norm_num) ]
  -- Now compute y^4.
  have eq5 : y^4 = (7 - Real.sqrt 13)/2 := by
    have eq6 : y^4 = (y^2) ^ 2 := by
      ring
    rw [eq6]
    rw [eq4]
    nlinarith [ Real.sqrt_nonneg 13, Real.sq_sqrt (show (13 : ℝ) ≥ (0 : ℝ) by norm_num) ]
  linarith [eq3, eq5]