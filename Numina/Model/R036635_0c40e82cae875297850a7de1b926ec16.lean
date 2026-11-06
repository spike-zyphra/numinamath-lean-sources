import Mathlib

open Real

theorem algebra_242553 {f : ℝ → ℝ} (hf : f = fun x => x + sqrt (x ^ 2 + 1) + 1 / (x - sqrt (x ^ 2 + 1))) :
    f 2015 = 0 := by
  rw [hf]
  have h1 : (2015 : ℝ) - Real.sqrt (2015 ^ 2 + 1) ≠ 0 := by
    by_contra h
    have h2 : Real.sqrt (2015 ^ 2 + 1) = (2015 : ℝ) := by linarith
    have h3 : Real.sqrt (2015 ^ 2 + 1) ^ 2 = (2015 : ℝ) ^ 2 := by
      rw [h2]
      all_goals nlinarith
    have h4 : Real.sqrt (2015 ^ 2 + 1) ^ 2 = (2015 ^ 2 + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (2015 ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (2015 ^ 2 + 1 : ℝ) by positivity)]
  have h2 :  1 / (2015 - Real.sqrt (2015 ^ 2 + 1)) = - (2015 + Real.sqrt (2015 ^ 2 + 1)) := by
    field_simp [show (2015 : ℝ) - Real.sqrt (2015 ^ 2 + 1) ≠ 0 by assumption, h1]
    <;> nlinarith [Real.sqrt_nonneg (2015 ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (2015 ^ 2 + 1 : ℝ) by positivity)]
  simp only [h2]
  all_goals nlinarith [Real.sqrt_nonneg (2015 ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (2015 ^ 2 + 1 : ℝ) by positivity)]