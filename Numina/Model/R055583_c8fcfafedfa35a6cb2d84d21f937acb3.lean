import Mathlib

open Real

theorem algebra_292589 (f : ℕ → ℝ)
    (h₀ : ∀ n, f n = tan (π / 7) ^ (2 * n) + tan (2 * π / 7) ^ (2 * n) + tan (3 * π / 7) ^ (2 * n)) :
    ∀ n, ∃ m, f n = m := by 
  intro n
  refine ⟨f n, rfl⟩