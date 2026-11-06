import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_148454 {a : ℕ → ℝ}
  (ha : ∀ n, a n = a 0 * r ^ n)
  (h₀ : a 0 = tan (π / 6))
  (h₁ : a 1 = sin (π / 3)) :
  a 2 = 3 * sqrt 3 / 4 := by
  have ha1 : a 1 = a 0 * r ^ 1 := by
    specialize ha 1
    simpa using ha
  have ha2 : a 2 = a 0 * r ^ 2 := by
    specialize ha 2
    simpa using ha
  have htan : tan (π / 6) = 1 / sqrt 3 := by 
    have htan1 : tan (π / 6) = sin (π / 6) / cos (π / 6) := by 
      rw [tan_eq_sin_div_cos]
    rw [htan1]
    have hsin : sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
    have hcos : cos (π / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
    rw [hsin, hcos]
    <;> field_simp
  have htan2 : a 0 = 1 / sqrt 3 := by
    rw [h₀]
    exact htan
  have hsin1 : a 1 = Real.sqrt 3 / 2 := by 
    rw [h₁]
    have sinus : sin (π / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
    linarith
  rw [show a 1 = a 0 * r ^ 1 by simpa using ha1] at hsin1
  rw [htan2] at hsin1
  have hr : r = 3 / 2 := by
    field_simp at hsin1 ⊢
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]
  rw [ha2]
  rw [htan2, hr]
  have hsqrt3 : sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 3)
  field_simp [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3)]
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0)]