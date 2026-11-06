import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_40613 (C : ℝ) :
  (∀ x : ℝ, sin x * cos x ≤ C * (sin x ^ 6 + cos x ^ 6)) ↔ C ≥ 2 := by
  constructor
  · -- Assume inequality holds for all x, prove C ≥ 2
    intro h
    have h1 := h (Real.pi / 4)
    have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
    have h3 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
    rw [h2, h3] at h1
    have h4 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by linarith), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by nlinarith)]
    have h5 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = 1 / 8 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 6 = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 3 := by ring
        _ = (1 / 2) ^ 3 := by rw [h4]
        _ = 1 / 8 := by norm_num
    have h6 : (Real.sqrt 2 / 2 : ℝ) ^ 6 + (Real.sqrt 2 / 2 : ℝ) ^ 6 = 1 / 4 := by
      linarith [h5]
    have h7 : (Real.sqrt 2 / 2 : ℝ) * (Real.sqrt 2 / 2 : ℝ) = 1 / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by linarith), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by nlinarith)]
    nlinarith [h6, h7]
  · -- Assume C ≥ 2, prove ∀ x : ℝ, sin x * cos x ≤ C * (sin x ^ 6 + cos x ^ 6)
    intro h x
    have h1 : sin x * cos x ≤ 2 * (sin x ^ 6 + cos x ^ 6) := by
      nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg ((sin x) - (cos x)), sq_nonneg (sin x * cos x), Real.sin_sq_add_cos_sq x, sq_nonneg ((sin x ^ 2) - 1 / 2), sq_nonneg ((cos x ^ 2) - 1 / 2), sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x * cos x - 1 / 2), sq_nonneg (sin x * cos x + 1 / 2)]
    have h2 : 2 * (sin x ^ 6 + cos x ^ 6) ≤ C * (sin x ^ 6 + cos x ^ 6) := by
      have h3 : (sin x ^ 6 + cos x ^ 6) ≥ 0 := by
        positivity
      nlinarith
    linarith [h1, h2]