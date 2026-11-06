import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_147489 {a : ℝ} (ha : 0 < a ∧ a ≠ 1) (F : ℝ → ℝ)
  (hF : Odd F) :
  Even (λ x => F x * (1 / (a ^ x - 1) + 1 / 2)) := by 
  rw [Even]
  use (fun x => (F x * (1 / (a ^ x - 1) + 1 / 2)) / 2)
  funext x
  simp
  all_goals ring