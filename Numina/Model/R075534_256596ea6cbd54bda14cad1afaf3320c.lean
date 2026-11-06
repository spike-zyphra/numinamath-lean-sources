import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_309428 (f : ℝ → ℝ) (hf : f = λ x => (3 * x ^ 2 + 6 * x + 5) / (1 / 2 * x ^ 2 + x + 1)) :
    IsLeast {y | ∃ x, y = f x} 4 := by
  constructor
  · -- Show 4 is achievable
    use -1
    rw [hf]
    norm_num
  · -- Show 4 is the smallest
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    have h1 : (3 * x ^ 2 + 6 * x + 5) / (1 / 2 * x ^ 2 + x + 1) ≥ 4 := by
      have h2 : (1 / 2 * x ^ 2 + x + 1) > 0 := by
        nlinarith [sq_nonneg x]
      have h3 : (3 * x ^ 2 + 6 * x + 5) ≥ 4 * (1 / 2 * x ^ 2 + x + 1) := by
        nlinarith [sq_nonneg (x + 1)]
      apply (le_div_iff₀ h2).mpr
      nlinarith
    simp at hx ⊢
    linarith [h1, hx]