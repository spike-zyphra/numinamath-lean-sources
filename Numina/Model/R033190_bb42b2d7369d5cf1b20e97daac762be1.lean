import Mathlib

open Real Set
open scoped Real

theorem calculus_16832 {x : ℝ} (hx : x > 0) (h : cos (arctan x) = x) :
    x^2 = (-1 + sqrt 5) / 2 := by 
  have h1 : cos (arctan x) = 1 / Real.sqrt (1 + x^2) := by 
    rw [cos_arctan]
  rw [h1] at h
  have h2 : 0 < (1 + x^2 : ℝ) := by
    nlinarith [sq_pos_of_pos hx]
  have h3 : Real.sqrt (1 + x^2) > 0 := by 
    apply Real.sqrt_pos.mpr 
    nlinarith [sq_pos_of_pos hx]
  have h4 : 1 = x * Real.sqrt (1 + x^2) := by
    field_simp [h3] at h ⊢
    <;> nlinarith
  have h7 : (1 : ℝ) = x^2 * (1 + x^2) := by
    have eq1 : (Real.sqrt (1 + x^2)) ^ 2 = 1 + x ^ 2 := by 
      rw [Real.sq_sqrt]
      positivity
    have eq2 : (1 : ℝ) = x ^ 2 * (1 + x ^ 2) := by 
      have eq3 : (x * Real.sqrt (1 + x^2)) ^ 2 = 1 := by 
        calc 
          (x * Real.sqrt (1 + x^2)) ^ 2 = (1 : ℝ) ^ 2 := by
            rw [show x * Real.sqrt (1 + x^2) = (1 : ℝ) by linarith [h4] ]
          _ = (1 : ℝ) := by 
            nlinarith
      have eq4 : (x * Real.sqrt (1 + x^2)) ^ 2 = x^2 * (1 + x^2) := by 
        calc 
          (x * Real.sqrt (1 + x^2)) ^ 2 = x^2 * (Real.sqrt (1 + x^2) ^ 2) := by 
            ring_nf 
          _ = x^2 * (1 + x^2) := by 
            rw [eq1]
      nlinarith [eq3, eq4]
    linarith [eq2]
  have h8 : x^2 > 0 := by 
    nlinarith [sq_pos_of_pos hx]
  have h9 : (x^2) = (-1 + Real.sqrt 5) / 2 := by 
    have h7' : (x^2) ^ 2 + x^2 - 1 = 0 := by 
      nlinarith [h7]
    have h10 : (x^2 - (-1 + Real.sqrt 5) / 2) * (x^2 - (-1 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [h7', Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- First factor is zero, which is the positive root.
      linarith 
    · -- Second factor is zero, which is the negative root.
      have h13 : x^2 < 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      linarith [show x ^ 2 ≥ 0 by positivity, h13]
  linarith [h9]