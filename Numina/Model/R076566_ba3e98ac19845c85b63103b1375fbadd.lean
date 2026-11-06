import Mathlib

theorem algebra_88343 {a b c : ℝ} (ha : a ≠ 0) (f g : ℝ → ℝ)
    (hf : f = fun x => a * (x + 5) ^ 2 + b * (x + 5) + c)
    (hg : g = fun x => -a * (x - 5) ^ 2 - b * (x - 5) - c) :
    ∃ m c, ∀ x, (f x + g x) = m * x + c := by
  use 20 * a, 10 * b
  intro x
  simp [hf, hg]
  ring