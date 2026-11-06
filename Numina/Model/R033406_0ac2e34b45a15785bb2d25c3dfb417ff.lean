import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_166671 {f : ℝ → ℝ} (hf : f = λ x => (1/3)^x) :
    ∀ x ∈ Ici (-1), f x ∈ Ioc 0 3 := by
  intro x hx
  rw [hf]
  have h1 : (1 / 3 : ℝ) ^ x > 0 := by positivity
  have h2 : (1 / 3 : ℝ) ^ x ≤ (3 : ℝ) := by
    have h3 : x ≥ -1 := by
      simpa using hx
    have h4 : (1 / 3 : ℝ) ^ x ≤ (1 / 3 : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_ge
      all_goals linarith
    have h5 : (1 / 3 : ℝ) ^ (-1 : ℝ) = (3 : ℝ) := by
      norm_num
    have h6 : (1 / 3 : ℝ) ^ (-1 : ℝ) = (3 : ℝ) := by linarith
    linarith [h5, h4]
  constructor
  · -- Show that $0 < (1/3)^x$
    linarith
  · -- Show that $(1/3)^x \leq 3$
    linarith