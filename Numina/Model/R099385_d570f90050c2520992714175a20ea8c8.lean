import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_159595 {f : ℝ → ℝ → ℝ}
  (hf : f = λ x y => 6 * y) :
  ∃ x y r : ℝ, x > 0 ∧ y > 0 ∧ r > 0 ∧
  f x y = 6 * y ↔ x = r ^ ((1 : ℝ) / 3) ∧ y = x * sqrt (r ^ ((1 : ℝ) / 3)) := by
    use 1, 1, 1
    norm_num [hf]
    <;> ring_nf <;> norm_num