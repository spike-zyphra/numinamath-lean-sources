import Mathlib

theorem other_91315 (a : ℚ) (b c d : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x ∈ Set.Icc (-1) 1)
    (h₁ : ∀ x, f (x + a + b) - f (x + b) = c * (x + 2 * a + ⌊x⌋ - 2 * ⌊x + a⌋ - ⌊b⌋) + d) :
    ∃ p, Function.Periodic f p := by
  use 0
  simp [Function.Periodic]