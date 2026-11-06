import Mathlib

open Real Complex Polynomial

theorem calculus_55756 {z : ℂ} (hz : z = (sqrt 2 + I * sqrt 2) / 2) :
    ∃ a b : ℝ, ∑ k in Finset.range 14, 1 / (1 - z * exp (k * I * π / 7)) = a - b * I := by 
  use (∑ k in Finset.range 14, 1 / (1 - z * exp (k * I * π / 7))).re, - (∑ k in Finset.range 14, 1 / (1 - z * exp (k * I * π / 7))).im
  simp [hz, Complex.ext_iff, Finset.sum_congr]
  all_goals try norm_num
  <;> aesop