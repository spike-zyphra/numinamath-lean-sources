import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_597674 {C : ℝ} :
  (∀ x y : ℝ, x ≠ y → x * y = 2 → ((x + y)^2 - 6) * ((x - y)^2 + 8) / (x - y)^2 ≥ C) ↔
  C ≤ 18 := by
  constructor
  · -- First direction: assuming the inequality, proving C ≤ 18
    intro h
    have h1 := h (1 + Real.sqrt 3) (Real.sqrt 3 - 1) (by
      -- Show that 1 + Real.sqrt 3 ≠ Real.sqrt 3 - 1
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    ) (by
      -- Show that (1 + Real.sqrt 3) * (Real.sqrt 3 - 1) = 2
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    )
    have h2 : ((1 + Real.sqrt 3 + (Real.sqrt 3 - 1)) ^ 2 - 6) * ((1 + Real.sqrt 3 - (Real.sqrt 3 - 1)) ^ 2 + 8) / ( (1 + Real.sqrt 3) - (Real.sqrt 3 - 1) ) ^ 2 = (18 : ℝ) := by
      have h3 : (1 + Real.sqrt 3 + (Real.sqrt 3 - 1)) = 2 * Real.sqrt 3 := by
        ring
      have h4 : (1 + Real.sqrt 3 - (Real.sqrt 3 - 1) ) = (2 : ℝ) := by
        ring
      have h5 : (1 + Real.sqrt 3 + (Real.sqrt 3 - 1) ) ^ 2 = 12 := by
        rw [h3]
        have hsqrt3 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        nlinarith [hsqrt3]
      have h6 : (1 + Real.sqrt 3 - (Real.sqrt 3 - 1) ) ^ 2 = 4 := by
        rw [h4]
        norm_num
      have eq1 : ((1 + Real.sqrt 3 + (Real.sqrt 3 - 1)) ^ 2 - 6) * ((1 + Real.sqrt 3 - (Real.sqrt 3 - 1)) ^ 2 + 8) = (72 : ℝ) := by
        rw [show (1 + Real.sqrt 3 + (Real.sqrt 3 - 1)) ^ 2 = (12 : ℝ) by linarith [h5] ]
        rw [show (1 + Real.sqrt 3 - (Real.sqrt 3 - 1)) ^ 2 = (4 : ℝ) by linarith [h6] ]
        norm_num
      have eq2 : ( (1 + Real.sqrt 3) - (Real.sqrt 3 - 1) ) ^ 2 = (4 : ℝ) := by
        nlinarith [h4]
      rw [eq1, eq2]
      all_goals norm_num
    have h3 : (18 : ℝ) ≥ C := by
      have eq1 : ((1 + Real.sqrt 3 + (Real.sqrt 3 - 1)) ^ 2 - 6) * ((1 + Real.sqrt 3 - (Real.sqrt 3 - 1)) ^ 2 + 8) / ( (1 + Real.sqrt 3) - (Real.sqrt 3 - 1) ) ^ 2 = (18 : ℝ) := h2
      linarith [h1, eq1]
    linarith [h3]
  · -- Second direction: proving the inequality given C ≤ 18
    intro h
    intro x y hneq hxy
    have h1 : ((x + y)^2 - 6) * ((x - y)^2 + 8) / (x - y)^2 ≥ 18 := by
      have pos1 : (x - y) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        intro h1
        apply hneq
        linarith
      have h2 : ((x + y) ^ 2 - 6) * ((x - y) ^ 2 + 8) ≥ 18 * (x - y) ^ 2 := by
        nlinarith [sq_nonneg (x * y - 2), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * (x - y)), sq_nonneg (y * (x - y)), sq_nonneg (x ^ 2 + y ^ 2 - 4), sq_nonneg ((x + y) ^ 2 - 12), sq_nonneg ((x - y) ^ 2 - 4), hxy, sq_nonneg (x * y)]
      apply (le_div_iff₀ (by positivity)).mpr
      linarith [h2]
    linarith [h1, h]