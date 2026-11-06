import Mathlib

open Real
open scoped BigOperators

theorem inequalities_158281 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0)
  (h₂ : c > 0) (h₃ : a^2 + b^2 = c^2) :
  a + b ≤ c * sqrt 2 ∧
  (a + b = c * sqrt 2 ↔ a = b) := by

  have h4 : (a + b) ^ 2 ≤ 2 * c ^ 2 := by
    nlinarith [sq_nonneg (a - b), h₃]

  have h5 : a + b ≤ c * Real.sqrt 2 := by
    have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [h4, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), mul_pos h₂ (show 0 < (Real.sqrt 2 : ℝ) by positivity)]

  have h_eq_iff : a + b = c * Real.sqrt 2 ↔ a = b := by
    constructor
    · -- Assume equality holds, prove a = b
      intro h_eq
      have h7 : (a + b) ^ 2 = 2 * c ^ 2 := by
        calc
          (a + b) ^ 2 = (c * Real.sqrt 2) ^ 2 := by
            rw [h_eq]
          _ = c ^ 2 * (Real.sqrt 2 ^ 2) := by ring
          _ = c ^ 2 * 2 := by
            rw [Real.sq_sqrt]
            norm_num
          _ = 2 * c ^ 2 := by ring

      have h8 : (a - b) ^ 2 = 0 := by
        nlinarith [h₃, h7]

      have h9 : a - b = 0 := by
        apply pow_eq_zero 
        exact h8

      linarith

    · -- Assume a = b, prove equality holds
      intro h_eq
      have h10 : a = b := h_eq

      have h11 : c ^ 2 = 2 * a ^ 2 := by
        rw [show b = a by linarith [h10] ] at h₃
        nlinarith

      have h13 : c * Real.sqrt 2 = 2 * a := by
        have h12 : c = Real.sqrt (2 * a ^ 2) := by
          have h13 : c > 0 := h₂
          have h14 : c ^ 2 = 2 * a ^ 2 := h11
          have h15 : c = Real.sqrt (2 * a ^ 2) := by
            rw [←h14]
            field_simp [h13]
          exact h15

        rw [h12]
        have h14 : Real.sqrt (2 * a ^ 2) = Real.sqrt 2 * Real.sqrt (a ^ 2) := by
          rw [Real.sqrt_mul (by positivity)]

        have h15 : Real.sqrt (a ^ 2) = a := by
          rw [Real.sqrt_sq (show 0 ≤ a by linarith)]

        rw [h14, h15]
        have h16 : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = (2 : ℝ) := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]

        nlinarith [h16, h₀]

      have h14 : a + b = 2 * a := by
        nlinarith [h10, h₀]

      linarith [h13, h14]

  constructor
  · exact h5
  · exact h_eq_iff