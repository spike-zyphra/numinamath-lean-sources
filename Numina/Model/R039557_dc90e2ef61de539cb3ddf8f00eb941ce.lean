import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_129121 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (3 * x ^ 2 + 6 * x + 5) / (1 / 2 * x ^ 2 + x + 1)) :
  IsLeast (range f) 4 := by
  have h1 : ∀ x, f x = (3 * x ^ 2 + 6 * x + 5) / (1 / 2 * x ^ 2 + x + 1) := by
    intro x
    specialize h₀ x
    simpa using h₀

  have h2 : 4 ∈ range f := by
    use -1
    rw [h1]
    norm_num

  have h3 : ∀ y, y ∈ range f → 4 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h1] at hx
    have h4 : (3 * x ^ 2 + 6 * x + 5) / (1 / 2 * x ^ 2 + x + 1) ≥ 4 := by
      have h5 : 1 / 2 * x ^ 2 + x + 1 > 0 := by
        nlinarith [sq_nonneg (x + 1)]
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith [sq_nonneg (x + 1)]
    linarith [h4, hx]

  constructor
  · -- Show that 4 is in the range
    exact h2
  · -- Show that 4 is the minimum
    intro y hy
    have h4 : 4 ≤ y := h3 y hy
    linarith