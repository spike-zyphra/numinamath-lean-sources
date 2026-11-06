import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_82865 :

    (IsGreatest {f | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x ≠ y ∧ (x ^ 2 + y ^ 2) / (x + y) ≤ 4 ∧ f = y - 2 * x} 4 ∧ IsLeast {f | ∃ x y : ℝ, x ≥ 0 ∧ y ≥ 0 ∧ x ≠ y ∧ (x ^ 2 + y ^ 2) / (x + y) ≤ 4 ∧ f = y - 2 * x} (-2 - 2 * sqrt 10)) := by
  constructor
  · -- Show that 4 is the greatest element in the set
    constructor
    · -- Show that 4 is in the set
      use 0, 4
      norm_num
    · -- Show that 4 is an upper bound
      intro f hf
      rcases hf with ⟨x, y, hx, hy, hxy, h1, hf⟩
      have h2 : x + y > 0 := by
        by_contra h
        push_neg at h
        have h3 : x + y = 0 := by linarith [show x ≥ 0 by linarith, show y ≥ 0 by linarith, h]
        have h4 : x = 0 := by nlinarith
        have h5 : y = 0 := by nlinarith
        have h6 : x = y := by linarith
        tauto
      have h3 : x ^ 2 + y ^ 2 ≤ 4 * (x + y) := by
        have h4 : (x ^ 2 + y ^ 2) / (x + y) ≤ 4 := h1
        apply (div_le_iff₀ (by linarith)).mp at h4
        linarith
      nlinarith [sq_nonneg (x - 0), sq_nonneg (y - 4), sq_pos_of_ne_zero (show (x - y) ≠ 0 by
        intro h'
        have h8 : x = y := by linarith
        tauto
      )]
  · -- Show that -2 - 2 * sqrt 10 is the least element in the set
    constructor
    · -- Show that -2 - 2 * sqrt 10 is in the set
      use 2 + 4 * Real.sqrt 10 / 5, 2 - 2 * Real.sqrt 10 / 5
      constructor
      · -- Show x ≥ 0
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), sq_nonneg (Real.sqrt 10 - 3), sq_nonneg (Real.sqrt 10 ^ 2 - 10)]
      constructor
      · -- Show y ≥ 0
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), sq_nonneg (Real.sqrt 10 - 5)]
      constructor
      · -- Show x ≠ y
        by_contra h
        have h1 : Real.sqrt 10 = 0 := by
          nlinarith
        have h2 : Real.sqrt 10 > 0 := by positivity
        linarith
      constructor
      · -- Show (x^2+y^2)/(x+y) ≤ 4
        have h7 : ((2 + 4 * Real.sqrt 10 / 5 : ℝ) ^ 2 + (2 - 2 * Real.sqrt 10 / 5 : ℝ) ^ 2) / ((2 + 4 * Real.sqrt 10 / 5 : ℝ) + (2 - 2 * Real.sqrt 10 / 5 : ℝ)) ≤ 4 := by
          have h7 : ((2 + 4 * Real.sqrt 10 / 5 : ℝ) ^ 2 + (2 - 2 * Real.sqrt 10 / 5 : ℝ) ^ 2) ≤ 4 * ((2 + 4 * Real.sqrt 10 / 5 : ℝ) + (2 - 2 * Real.sqrt 10 / 5 : ℝ)) := by
            nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), sq_nonneg (Real.sqrt 10 ^ 2 - 10)]
          have h8 : ((2 + 4 * Real.sqrt 10 / 5 : ℝ) ^ 2 + (2 - 2 * Real.sqrt 10 / 5 : ℝ) ^ 2) / ((2 + 4 * Real.sqrt 10 / 5 : ℝ) + (2 - 2 * Real.sqrt 10 / 5 : ℝ)) ≤ 4 := by
            apply (div_le_iff₀ (by
              nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
            )).mpr
            linarith
          linarith
        linarith
      · -- Show f = y - 2 * x
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    · -- Show that -2 - 2 * sqrt 10 is the least element in the set
      intro f hf
      rcases hf with ⟨x, y, hx, hy, hxy, h1, hf⟩
      have h2 : x + y > 0 := by
        by_contra h
        push_neg at h
        have h3 : x + y = 0 := by linarith [show x ≥ 0 by linarith, show y ≥ 0 by linarith, h]
        have h4 : x = 0 := by nlinarith
        have h5 : y = 0 := by nlinarith
        have h6 : x = y := by linarith
        tauto
      have h3 : x ^ 2 + y ^ 2 ≤ 4 * (x + y) := by
        have h4 : (x ^ 2 + y ^ 2) / (x + y) ≤ 4 := h1
        apply (div_le_iff₀ (by linarith)).mp at h4
        linarith
      have h7 : y - 2 * x ≥ -2 - 2 * Real.sqrt 10 := by
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), sq_nonneg (x - (2 + 4 * Real.sqrt 10 / 5)), sq_nonneg (y - (2 - 2 * Real.sqrt 10 / 5)), sq_pos_of_ne_zero (show (x - y) ≠ 0 by
          intro h'
          have h8 : x = y := by linarith
          tauto
        ), sq_nonneg (y - 2), sq_nonneg (x - 2)]
      linarith