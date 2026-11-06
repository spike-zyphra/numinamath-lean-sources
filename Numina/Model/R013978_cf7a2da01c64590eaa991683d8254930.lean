import Mathlib

open Real

theorem algebra_185964 (f : ℕ → ℝ)
    (h₀ : ∀ n, f n = tan (π / 7) ^ (2 * n) + tan (2 * π / 7) ^ (2 * n) +
      tan (3 * π / 7) ^ (2 * n)) :
    ∀ n, ∃ m, f n = m := by 
  intro n 
  have h3 : f n = tan (π / 7) ^ (2 * n) + tan (2 * π / 7) ^ (2 * n) + tan (3 * π / 7) ^ (2 * n) := h₀ n 
  refine' ⟨tan (π / 7) ^ (2 * n) + tan (2 * π / 7) ^ (2 * n) + tan (3 * π / 7) ^ (2 * n), h3⟩
  all_goals linarith