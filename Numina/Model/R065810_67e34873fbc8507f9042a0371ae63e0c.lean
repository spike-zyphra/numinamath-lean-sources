import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_327278 {a b : ℝ} (ha : a > b) (h : a + b = 2) :
    (a^2 + b^2) / (a - b) ≥ 2 := by
  have h1 : a - b > 0 := by linarith
  have h2 : a ^ 2 + b ^ 2 ≥ 2 * (a - b) := by
    have h11 : b = 2 - a := by linarith
    rw [h11]
    nlinarith [sq_nonneg (a - 2), sq_nonneg ((2 - a) - 0), sq_nonneg ((2 - a) - a)]
  have h4 : (a^2 + b^2) / (a - b) - 2 ≥ 0 := by
    have h5 : (a^2 + b^2) / (a - b) - 2 = (a ^ 2 + b ^ 2 - 2 * (a - b)) / (a - b) := by
      field_simp
      <;> ring
    rw [h5]
    have h6 : (a ^ 2 + b ^ 2 - 2 * (a - b)) ≥ 0 := by linarith
    have h7 : a - b > 0 := by linarith
    exact div_nonneg h6 (by linarith)
  linarith