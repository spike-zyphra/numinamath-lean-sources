import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_87703 (z : ℂ) :
  (abs z)^2 + 2 * abs (z - 1) ≥ 1 ∧ ((abs z)^2 + 2 * abs (z - 1) = 1 ↔ z = 1) := by
  have h1 : (abs z) ^ 2 + 2 * abs (z - 1) ≥ 1 := by
    have h2 : abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq]
      all_goals ring
    have h3 : abs (z - 1) = Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) := by
      simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
      all_goals ring
    rw [h2, h3]
    have h4 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h5 : Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) ≥ Real.sqrt ((z.re - 1) ^ 2) := by
      apply Real.sqrt_le_sqrt
      have h7 : (z.re - 1) ^ 2 ≤ (z.re - 1) ^ 2 + z.im ^ 2 := by
        linarith [sq_nonneg z.im]
      linarith
    have h6 : Real.sqrt ((z.re - 1) ^ 2) = |z.re - 1| := by
      rw [Real.sqrt_sq_eq_abs]
    have h7 : 2 * Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) ≥ 2 * |z.re - 1| := by
      have h8 : Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) ≥ Real.sqrt ((z.re - 1) ^ 2) := h5
      have h9 : Real.sqrt ((z.re - 1) ^ 2) = |z.re - 1| := h6
      linarith [h9]
    have h11 : z.re ^ 2 + 2 * |z.re - 1| ≥ 1 := by
      cases' abs_cases (z.re - 1) with h h <;>
        nlinarith [sq_nonneg (z.re - 1)]
    nlinarith [Real.sqrt_nonneg ((z.re - 1) ^ 2 + z.im ^ 2), Real.sqrt_nonneg ((z.re - 1) ^ 2)]
  have h11 : (abs z) ^ 2 + 2 * abs (z - 1) = 1 ↔ z = 1 := by
    constructor
    · -- Assume (abs z) ^ 2 + 2 * abs (z - 1) = 1, prove z = 1
      intro h_eq
      have h21 : abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        all_goals ring
      have h22 : abs (z - 1) = Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) := by
        simp [Complex.abs, Complex.normSq, Complex.re, Complex.im]
        all_goals ring
      rw [h21, h22] at h_eq
      have h10 : z.re ^ 2 + z.im ^ 2 + 2 * Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) = 1 := by
        have h4 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        nlinarith [Real.sqrt_nonneg ((z.re - 1) ^ 2 + z.im ^ 2)]
      have h17 : z.im ^ 2 = 0 := by
        have h24 : z.re ^ 2 + 2 * Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) + z.im ^ 2 ≥ 1 := by 
          have h25 : Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) ≥ Real.sqrt ((z.re - 1) ^ 2) := by 
            apply Real.sqrt_le_sqrt
            have h26 : (z.re - 1) ^ 2 ≤ (z.re - 1) ^ 2 + z.im ^ 2 := by linarith [sq_nonneg z.im]
            linarith
          have h27 : Real.sqrt ((z.re - 1) ^ 2) = |z.re - 1| := by 
            rw [Real.sqrt_sq_eq_abs]
          have h29 : 2 * Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) ≥ 2 * |z.re - 1| := by 
            have h30 : Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) ≥ Real.sqrt ((z.re - 1) ^ 2) := h25
            have h31 : Real.sqrt ((z.re - 1) ^ 2) = |z.re - 1| := h27
            nlinarith [h31]
          have h32 : z.re ^ 2 ≥ z.re ^ 2 := by nlinarith
          have h33 : z.re ^ 2 + 2 * Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) ≥ z.re ^ 2 + 2 * |z.re - 1| := by 
            nlinarith [Real.sqrt_nonneg ((z.re - 1) ^ 2 + z.im ^ 2)]
          have h34 : z.re ^ 2 + 2 * |z.re - 1| ≥ 1 := by 
            cases' abs_cases (z.re - 1) with h h <;> 
              nlinarith [sq_nonneg (z.re - 1)]
          nlinarith [abs_nonneg (z.re - 1), sq_nonneg (z.re ^ 2 + z.im ^ 2 - 1), sq_nonneg (z.re - 1), sq_nonneg (z.im ^ 2), sq_nonneg (z.re ^ 2), abs_nonneg (z.re - 1)]
        nlinarith [Real.sqrt_nonneg ((z.re - 1) ^ 2 + z.im ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ (z.re - 1) ^ 2 + z.im ^ 2 by positivity), sq_nonneg (z.re ^ 2 + z.im ^ 2 - 1)]
      have h26 : z.re ^ 2 + 2 * Real.sqrt ((z.re - 1) ^ 2) = 1 := by
        have h27 : z.im ^ 2 = 0 := h17
        have h28 : Real.sqrt ((z.re - 1) ^ 2 + z.im ^ 2) = Real.sqrt ((z.re - 1) ^ 2) := by
          have h30 : z.im ^ 2 = 0 := h27
          have h31 : (z.re - 1) ^ 2 + z.im ^ 2 = (z.re - 1) ^ 2 := by 
            nlinarith 
          rw [h31] 
        have h28' : z.re ^ 2 + z.im ^ 2 = z.re ^ 2 := by
          nlinarith [h17] 
        nlinarith [Real.sqrt_nonneg ((z.re - 1) ^ 2 + z.im ^ 2), h28, Real.sq_sqrt (show (0 : ℝ) ≤ (z.re - 1) ^ 2 by positivity)]
      have h30 : z.re = 1 := by
        have h31 : Real.sqrt ((z.re - 1) ^ 2) ≥ 0 := by positivity
        have h32 : Real.sqrt ((z.re - 1) ^ 2) = |z.re - 1| := by
          rw [Real.sqrt_sq_eq_abs]
        rw [show Real.sqrt ((z.re - 1) ^ 2) = |z.re - 1| by rw [h32]] at h26
        cases' abs_cases (z.re - 1) with h h 
        · -- When z.re - 1 ≥ 0, so |z.re - 1| = z.re - 1
          nlinarith
        · -- When z.re - 1 < 0, so |z.re - 1| = -(z.re - 1)
          nlinarith
      have h31 : z.im = 0 := by
        nlinarith [h17, sq_nonneg z.im]
      have h32 : z = 1 := by 
        simp [Complex.ext_iff, h30, h31]
      exact h32
    · -- If z = 1, then (abs z) ^ 2 + 2 * abs (z - 1) = 1.
      intro h_eq
      rw [h_eq]
      simp [Complex.abs, Complex.normSq]
  constructor
  · exact h1
  · exact h11