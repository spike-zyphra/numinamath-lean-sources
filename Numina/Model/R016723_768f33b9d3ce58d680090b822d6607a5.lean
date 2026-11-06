import Mathlib

theorem algebra_215842 (x : ℝ) (hx : x^2 + Real.sqrt 21 ≠ 0) :
    x^4 - x^2 * Real.sqrt 21 - 1 = 0 ↔ x = Real.sqrt ((Real.sqrt 21 + 5) / 2) ∨ x = -Real.sqrt ((Real.sqrt 21 + 5) / 2) := by
  constructor
  · -- Forward implication: Equation implies solutions
    intro h
    have h1 : (x^2) ^ 2 - Real.sqrt 21 * (x^2) - 1 = 0 := by linarith
    have h2 : ((x^2) - (Real.sqrt 21 + 5) / 2) * ((x^2) - (Real.sqrt 21 - 5) / 2) = 0 := by
      nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where x^2 = (Real.sqrt 21 + 5) / 2
      have h5 : x ^ 2 = (Real.sqrt 21 + 5) / 2 := by linarith
      have h8 : x = Real.sqrt ((Real.sqrt 21 + 5) / 2) ∨ x = -Real.sqrt ((Real.sqrt 21 + 5) / 2) := by
        apply eq_or_eq_neg_of_sq_eq_sq
        field_simp
        linarith
      tauto
    · -- Case where x^2 = (Real.sqrt 21 - 5) / 2
      have h7 : x ^ 2 = (Real.sqrt 21 - 5) / 2 := by linarith
      nlinarith [Real.sqrt_nonneg 21, h7, Real.sqrt_nonneg 21, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]
  · -- Backward implication: Solutions satisfy equation
    rintro (h | h)
    · -- Case where x = Real.sqrt ((Real.sqrt 21 + 5) / 2)
      have h1 : x = Real.sqrt ((Real.sqrt 21 + 5) / 2) := by linarith
      have h2 : x ^ 2 = (Real.sqrt 21 + 5) / 2 := by
        rw [h1]
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]
      nlinarith [Real.sqrt_nonneg 21, h2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]
    · -- Case where x = -Real.sqrt ((Real.sqrt 21 + 5) / 2)
      have h1 : x = -Real.sqrt ((Real.sqrt 21 + 5) / 2) := by linarith
      have h2 : x ^ 2 = (Real.sqrt 21 + 5) / 2 := by
        rw [h1]
        have h3 : (-Real.sqrt ((Real.sqrt 21 + 5) / 2)) ^ 2 = (Real.sqrt ((Real.sqrt 21 + 5) / 2)) ^ 2 := by ring_nf
        rw [h3]
        rw [Real.sq_sqrt]
        nlinarith [Real.sqrt_nonneg 21, Real.sqrt_nonneg ((Real.sqrt 21 + 5) / 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]
      nlinarith [Real.sqrt_nonneg 21, h2, Real.sqrt_nonneg ((Real.sqrt 21 + 5) / 2), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)]