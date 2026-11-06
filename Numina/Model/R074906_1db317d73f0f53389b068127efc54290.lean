import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_114224 {f : ℝ → ℝ} (hf : f = λ x => (5 - 4 * x + x ^ 2) / (2 - x)) :
    IsLeast {y | ∃ x, x < 2 ∧ f x = y} 2 := by
  constructor
  · -- Show that 2 belongs to the set because f(1) = 2
    use 1
    constructor
    · norm_num
    · -- Compute f(1) = 2
      rw [hf]
      norm_num
  · -- Show that 2 is the least element in the image
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    simp at hfx
    -- Show that y >= 2
    have h1 : (5 - 4 * x + x ^ 2) / (2 - x) ≥ 2 := by
      have hx2 : 2 - x > 0 := by linarith
      have h2 : 5 - 4 * x + x ^ 2 ≥ 2 * (2 - x) := by
        nlinarith [sq_nonneg (x - 1)]
      have h3 : (5 - 4 * x + x ^ 2) / (2 - x) ≥ 2 := by
        apply (le_div_iff₀ hx2).mpr
        linarith
      linarith
    -- Since y = f(x) and f(x) >= 2, so y >= 2
    linarith [hfx, h1]