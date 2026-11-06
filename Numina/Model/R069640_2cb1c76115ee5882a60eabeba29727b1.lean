import Mathlib

open Real

theorem calculus_144495 (f : ℝ → ℝ) (hf : f = fun x => 3 * x ^ ((1 : ℝ) / 4) - sqrt x) (x0 : ℝ) (hx0 : x0 = 1) :
    ∃ m c, ∀ x, x / 4 + 7 / 4 = f x0 + m * (x - x0) + c := by
  use 1 / 4
  use 0
  intro x
  rw [hx0]
  rw [hf]
  simp
  <;> ring_nf <;> norm_num