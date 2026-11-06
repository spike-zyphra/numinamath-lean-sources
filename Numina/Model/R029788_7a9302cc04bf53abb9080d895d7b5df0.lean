import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_198724 {f : ℝ → ℝ} :
  Even ((λ x => f x + f (-x)) / 2) ∧ Odd ((λ x => f x - f (-x)) / 2) := by

  constructor
  · -- Show that $y_1 = \frac{f(x)+f(-x)}{2}$ is even.
    unfold Even
    use fun x => (f x + f (-x)) / 4
    funext x
    simp
    <;> ring
  · -- Show that $y_2 = \frac{f(x)-f(-x)}{2}$ is odd.
    unfold Odd
    use fun x => (f x - f (-x) - 2) / 4
    funext x
    simp
    <;> ring