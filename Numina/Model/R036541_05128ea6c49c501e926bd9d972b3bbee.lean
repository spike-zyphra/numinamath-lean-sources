import Mathlib

open Real

theorem inequalities_82818 (C : ℝ) :
    (∀ x y : ℝ, y ≠ x → x * y = 2 → ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) / (x - y) ^ 2 ≥ C) ↔
    C ≤ 18 := by
  constructor
  · -- (∀ x y : ℝ, y ≠ x → x * y = 2 → ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) / (x - y) ^ 2 ≥ C) → C ≤ 18
    intro h
    have h1 := h (1 + Real.sqrt 3) (-1 + Real.sqrt 3) (by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      ) (by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      )
    have t1 : ((1 + Real.sqrt 3 : ℝ) + (-1 + Real.sqrt 3 : ℝ)) ^ 2 - (6 : ℝ) = (6 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have t2 : ((1 + Real.sqrt 3 : ℝ) - (-1 + Real.sqrt 3 : ℝ)) ^ 2 + (8 : ℝ) = (12 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have t3 : ((1 + Real.sqrt 3 : ℝ) - (-1 + Real.sqrt 3 : ℝ)) ^ 2 = (4 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    rw [t1, t2, t3] at h1
    norm_num at h1
    linarith
  · -- (C ≤ 18) → (∀ x y : ℝ, y ≠ x → x * y = 2 → ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) / (x - y) ^ 2 ≥ C)
    intro hc x y hne hx
    have h1 : x - y ≠ 0 := by
      intro h'
      apply hne
      linarith
    have h2 : (x * y) = 2 := hx
    have h4 : (x - y) ^ 2 > 0 := by
      apply sq_pos_of_ne_zero
      intro h'
      apply hne
      linarith
    have h8 : ((x + y) ^ 2) - (x - y) ^ 2 = 8 := by
      have h5 : x * y = 2 := h2
      nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y), sq_nonneg ((x + y) - (x - y))]
    have h9 : (x + y) ^ 2 = (x - y) ^ 2 + 8 := by
      nlinarith [h8]
    have h10 : ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) ≥ 18 * ((x - y) ^ 2) := by
      have h11 : ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) = ((x - y) ^ 2 + 2) * ((x - y) ^ 2 + 8) := by
        rw [show (x + y) ^ 2 = (x - y) ^ 2 + 8 by linarith [h9]]
        nlinarith
      rw [h11]
      nlinarith [sq_nonneg ((x - y) ^ 2 - 4), sq_nonneg ((x + y) ^ 2), sq_nonneg ((x - y) ^ 2), mul_pos (show (0 : ℝ) < (x - y) ^ 2 by positivity) (show (0 : ℝ) < (x - y) ^ 2 by positivity)]
    have h11 : ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) ≥ C * ((x - y) ^ 2) := by
      nlinarith [h10, hc]
    have h12 : ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) / (x - y) ^ 2 ≥ C := by
      have h13 : (x - y) ^ 2 > 0 := h4
      apply (le_div_iff₀ h13).mpr
      linarith [h11, sq_nonneg ((x - y) ^ 2)]
    linarith [h12]