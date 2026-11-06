import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem number_theory_27306 {f : Polynomial ℤ} (hf : ∀ n ≥ 2, Function.Surjective (λ x => f.eval x % n)) :
    ∃ b, f = X + b ∨ f = -X + b := by 
  use (f - X)
  left
  simp [sub_eq_add_neg, add_left_inj]
  <;> ring_nf <;> try tauto