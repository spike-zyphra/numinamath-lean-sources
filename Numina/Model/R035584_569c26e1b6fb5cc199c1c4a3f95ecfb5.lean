import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_237968 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
  (f : ℝ → ℝ → ℝ)
  (hf : f = λ a b => (b^2 + 2)/(a + b) + (a^2)/(a * b + 1)) :
  f a b ≥ 2 := by
  have h1 : f a b = (b ^ 2 + 2) / (a + b) + (a ^ 2) / (a * b + 1) := by
    rw [hf]

  rw [h1]
  have h2 : 0 < a + b := by linarith
  have h3 : 0 < a * b + 1 := by nlinarith
  have h4 : (b ^ 2 + 2) / (a + b) + (a ^ 2) / (a * b + 1) - 2 ≥ 0 := by
    have h5 : (b ^ 2 + 2) / (a + b) + (a ^ 2) / (a * b + 1) - 2 =
      ((b ^ 2 + 2) * (a * b + 1) + (a ^ 2) * (a + b) - 2 * (a + b) * (a * b + 1)) / ((a + b) * (a * b + 1)) := by
      field_simp
      <;> ring
    rw [h5] at *
    have h6 : (b ^ 2 + 2) * (a * b + 1) + (a ^ 2) * (a + b) - 2 * (a + b) * (a * b + 1) ≥ 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a * (b - 1)), sq_nonneg ((b) * (a - 1)), mul_pos ha hb, sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_nonneg (a * b * (a - b))]
    have h7 : (a + b) * (a * b + 1) > 0 := by positivity
    apply div_nonneg
    linarith
    all_goals positivity
  linarith