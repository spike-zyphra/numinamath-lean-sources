import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_104801 {f : ℝ → ℝ} (hf : f = λ x => 3^(x^2 - 2 * x)) :
    ∀ x ≤ 1, deriv f x ≤ 0 := by
  intro x hx
  rw [hf]
  have h1 : deriv (λ (y : ℝ) => (3 : ℝ) ^ (y^2 - 2 * y)) x =
      (3 : ℝ) ^ (x ^ 2 - 2 * x) * (2 * x - 2) * Real.log (3 : ℝ) := by
    simp [deriv_pow, deriv_sub, deriv_id'', mul_comm]
    <;> field_simp [Real.rpow_def_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num)]
    <;> ring_nf
    <;> norm_num
    <;> ring
  rw [h1]
  have h2 : x ≤ 1 := hx
  have h3 : (2 * x - 2) ≤ (0 : ℝ) := by
    linarith
  have h4 : Real.log (3 : ℝ) > 0 := by
    apply Real.log_pos
    all_goals norm_num
  have h5 : (3 : ℝ) ^ (x^2 - 2 * x) > 0 := by
    positivity
  have h5' : (2 * x - 2) * Real.log (3 : ℝ) ≤ (0 : ℝ) := by
    have h6 : (2 * x - 2 : ℝ) ≤ (0 : ℝ) := h3
    have h7 : Real.log (3 : ℝ) > 0 := h4
    nlinarith
  have h8 : (3 : ℝ) ^ (x^2 - 2 * x) * (2 * x - 2) * Real.log (3 : ℝ) ≤ (0 : ℝ) := by
    have h9 : (3 : ℝ) ^ (x^2 - 2 * x) > 0 := h5
    have h10 : (2 * x - 2) * Real.log (3 : ℝ) ≤ (0 : ℝ) := h5'
    have h10' : (3 : ℝ) ^ (x^2 - 2 * x) * ((2 * x - 2) * Real.log (3 : ℝ)) ≤ (0 : ℝ) := by
      nlinarith [h9, h10]
    have h11 : (3 : ℝ) ^ (x^2 - 2 * x) * (2 * x - 2) * Real.log (3 : ℝ) = (3 : ℝ) ^ (x^2 - 2 * x) * ((2 * x - 2) * Real.log (3 : ℝ)) := by
      ring
    linarith [h11, h10']
  linarith