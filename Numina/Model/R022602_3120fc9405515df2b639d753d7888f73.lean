import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_103061 {a : ℝ} (ha : 0 < a ∧ a ≠ 1)
  (F : ℝ → ℝ) (hF : Odd F) :
  Even (λ x => F x * (1 / (a ^ x - 1) + 1 / 2)) := by
  rw [Even]
  use λ x => (F x * (1 / (a ^ x - 1) + 1 / 2) ) / 2
  funext x
  have h5 : F x * (1 / (a ^ x - 1) + 1 / 2) = (F x * (1 / (a ^ x - 1) + 1 / 2) ) / 2 + (F x * (1 / (a ^ x - 1) + 1 / 2) ) / 2 := by
    ring_nf
  simpa using h5