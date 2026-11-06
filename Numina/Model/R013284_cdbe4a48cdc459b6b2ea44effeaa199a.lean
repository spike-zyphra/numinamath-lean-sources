import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303941 {f g : ℝ → ℝ}
  (hf : f = λ x => sqrt (1 - x^2) / (abs (x + 2) - 2))
  (hg : g = λ x => log (sqrt (1 + x^2) - x)) :
  Odd (λ x => f x * g x) ∧ Even (λ x => f x * g x) := by
  constructor
  · -- Show that F is odd
    use (λ x => (f x * g x - 1) / 2)
    funext x
    simp
    <;> ring_nf
  · -- Show that F is even
    use (λ x => (f x * g x) / 2)
    funext x
    simp
    <;> ring_nf