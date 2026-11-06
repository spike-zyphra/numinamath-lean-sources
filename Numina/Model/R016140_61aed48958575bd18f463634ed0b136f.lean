import Mathlib

theorem algebra_190168 (A B C : ℝ) (f : ℝ → ℝ) (hf : f = fun z => z^3 + A * z^2 + B * z + C) :
    ∃ p q β, ∀ z, f z = (z - β)^3 + p * (z - β) + q := by
  use B - A ^ 2 / 3
  use 2 * A ^ 3 / 27 - A * B / 3 + C
  use -A / 3
  intro z
  rw [hf]
  simp
  ring