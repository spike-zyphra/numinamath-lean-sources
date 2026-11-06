import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_133461 (α : ℝ) (hα : α ∈ Ioo 0 π)
  (h : α + 70 + 100 = π ∨ α + 130 + 150 = π) :
  30 < α ∧ α < 170 ∨ 20 < α ∧ α < 80 := by
  rcases hα with ⟨hα1, hα2⟩
  rcases h with (h | h)
  · -- Assume α + 70 + 100 = π
    exfalso
    have h1 : α = π - 170 := by
      linarith
    have h2 : α > 0 := hα1
    have h3 : α < (0 : ℝ) := by
      linarith [Real.pi_lt_31416]
    linarith
  · -- Assume α + 130 + 150 = π
    exfalso
    have h1 : α = π - 280 := by
      linarith
    have h2 : α > 0 := hα1
    have h3 : α < (0 : ℝ) := by
      linarith [Real.pi_lt_31416]
    linarith