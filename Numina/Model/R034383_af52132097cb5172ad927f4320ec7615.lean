import Mathlib

open Real Set
open scoped Real

theorem algebra_236794 (x y : ℝ) (h : sin x + sin y = 1) :
    -sqrt 3 ≤ cos x + cos y ∧ cos x + cos y ≤ sqrt 3 := by

  have h1 : (cos x + cos y) ^ 2 ≤ 3 := by
    have h2 : (sin x + sin y) ^ 2 = 1 := by
      rw [h]
      norm_num

    have h4 : (cos x + cos y) ^ 2 = 1 + 2 * cos (x - y) := by 
      have h32 : (cos x + cos y) ^ 2 + (sin x + sin y) ^ 2 = 2 * (1 + cos (x - y)) := by
        have h11 : (cos x + cos y) ^ 2 + (sin x + sin y) ^ 2 = (cos x) ^ 2 + (cos y) ^ 2 + 2 * (cos x * cos y) + (sin x) ^ 2 + (sin y) ^ 2 + 2 * (sin x * sin y) := by 
          ring_nf
        have h12 : (cos x) ^ 2 + (sin x) ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq x
        have h13 : (cos y) ^ 2 + (sin y) ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq y
        have h14 : (cos x) ^ 2 + (cos y) ^ 2 + 2 * (cos x * cos y) + (sin x) ^ 2 + (sin y) ^ 2 + 2 * (sin x * sin y) = 2 * (1 + cos (x - y)) := by
          have h21 : cos (x - y) = cos x * cos y + sin x * sin y := by
            rw [cos_sub]
          have h22 : (cos x) ^ 2 + (sin x) ^ 2 = 1 := by
            exact Real.cos_sq_add_sin_sq x
          have h23 : (cos y) ^ 2 + (sin y) ^ 2 = 1 := by
            exact Real.cos_sq_add_sin_sq y
          linarith [h21, h22, h23]
        linarith [h11, h12, h13, h14]
      nlinarith [h32, h2]
    
    have h5 : cos (x - y) ≤ 1 := by
      have h6 : cos (x - y) ≤ 1 := by
        apply cos_le_one
      linarith
    nlinarith [h4, h5]

  constructor
  · -- -sqrt 3 ≤ cos x + cos y
    have h7 : -sqrt 3 ≤ cos x + cos y := by
      have h8 : (cos x + cos y) ^ 2 ≤ 3 := h1
      have h9 : -sqrt 3 ≤ cos x + cos y := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (cos x + cos y + sqrt 3)]
      exact h9
    exact h7
  · -- cos x + cos y ≤ sqrt 3
    have h8 : cos x + cos y ≤ sqrt 3 := by
      have h9 : (cos x + cos y) ^ 2 ≤ 3 := h1
      have h11 : cos x + cos y ≤ sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), sq_nonneg (cos x + cos y - sqrt 3)]
      exact h11
    exact h8