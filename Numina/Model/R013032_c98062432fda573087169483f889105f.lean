import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21991 {f g : ℝ → ℝ}
  (hf : Odd f) (hg : Odd g) :
  Even (λ x => f x * g x) := by 
  unfold Even
  use (λ x => (f x * g x) / 2)
  funext x
  <;> ring_nf 
  <;> simp
  <;> ring_nf <;> simp [div_add_div_same, mul_add, add_assoc]
  <;> ring_nf