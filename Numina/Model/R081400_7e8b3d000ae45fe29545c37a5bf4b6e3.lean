import Mathlib

open Real Set

theorem algebra_150503 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = (x^2 + 4 * x + 5) * (x^2 + 4 * x + 2) + 2 * x^2 + 8 * x + 1) :
    IsLeast (range f) (-9) := by
  constructor
  · -- Show -9 is attained
    use -2
    norm_num [h₀]
  · -- Show -9 is the least value
    intro y
    rintro ⟨x, hx⟩
    rw [h₀ x] at hx
    nlinarith [sq_nonneg ((x + 2) ^ 2), sq_nonneg ((x + 2) ^ 2 - 1 / 2), sq_nonneg (x + 2), sq_nonneg ((x + 2) ^ 2 - 1), sq_nonneg ((x + 2) ^ 2 - 2)]