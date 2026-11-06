import Mathlib

open Real Set

theorem inequalities_33949 :
    IsLeast {C : ℝ | ∀ x y : ℝ, 1 + (x + y) ^ 2 ≤ C * (1 + x ^ 2) * (1 + y ^ 2)} (4 / 3) := by
  constructor
  · -- Show that 4/3 is in the set.
    intro x y
    have h : 1 + (x + y) ^ 2 ≤ (4 / 3) * (1 + x ^ 2) * (1 + y ^ 2) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - 1 / 2), sq_nonneg (x - 1 / Real.sqrt 2), sq_nonneg (y - 1 / Real.sqrt 2), sq_nonneg (x + y - Real.sqrt 2), sq_nonneg (x + y + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith
  · -- Show that 4/3 is the least such constant.
    intro C hC
    have h1 := hC (Real.sqrt 2 / 2) (Real.sqrt 2 / 2)
    have h2 : 1 + (Real.sqrt 2 / 2 + Real.sqrt 2 / 2) ^ 2 = 3 := by
      have h3 : Real.sqrt 2 / 2 + Real.sqrt 2 / 2 = Real.sqrt 2 := by ring
      rw [h3]
      have h4 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith
    have h3 : 1 + (Real.sqrt 2 / 2) ^ 2 = 3 / 2 := by
      have h4 : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
        have h5 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith
      linarith
    have h4 : 1 + (Real.sqrt 2 / 2 + Real.sqrt 2 / 2) ^ 2 = 3 := h2
    have h5 : 1 + (Real.sqrt 2 / 2) ^ 2 = 3 / 2 := h3
    rw [h4] at h1
    rw [h5] at h1
    have h6 : C * (3 / 2 : ℝ) * (3 / 2 : ℝ) = (9 / 4) * C := by
      ring_nf
    rw [h6] at h1
    linarith