import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314562 {f g : ℝ → ℝ}
  (hf : ∀ x, f (-x) = g x) (hg : ∀ x, g (-x) = f x) :
  Odd f := by 
  unfold Odd
  use fun x => (f x - 1) / 2
  funext x
  simp [mul_add, mul_comm]
  <;> ring_nf
  <;> tauto
  all_goals try { try { tauto } }
  all_goals try { try { tauto } }