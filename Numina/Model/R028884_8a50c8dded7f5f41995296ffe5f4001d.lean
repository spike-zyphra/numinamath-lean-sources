import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_196268 {f : ℝ → ℝ}
  (hf : ∀ x > 0, f x - 2 * x * f (1 / x) + x ^ 2 = 0) :
  IsLeast (Set.image f (Set.Ioi 0)) 1 := by
  have h1 : ∀ x > 0, f x = x ^ 2 / 3 + 2 / (3 * x) := by
    intro x hx
    have eq1 := hf x hx
    have eq2 := hf (1 / x) (by positivity)
    field_simp at eq2 ⊢
    ring_nf at eq1 eq2
    field_simp at *
    nlinarith [sq_pos_of_pos hx, sq_nonneg (x - 1)]
  have h1' : 1 ∈ Set.image f (Set.Ioi 0) := by
    use 1
    constructor
    · norm_num
    · rw [h1 1 (by norm_num)]
      norm_num
  constructor
  · -- Show 1 is in the image
    exact h1'
  · -- Show that 1 is the minimum
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx' : x > 0 := by
      simpa using hx
    have eq1 : f x = x ^ 2 / 3 + 2 / (3 * x) := h1 x hx'
    rw [eq1] at hfx
    have h2 : x ^ 2 / 3 + 2 / (3 * x) ≥ 1 := by
      have hx' : x > 0 := by
        linarith
      have h3 : x ^ 2 / 3 + 2 / (3 * x) - 1 ≥ 0 := by
        have h4 : x ^ 2 / 3 + 2 / (3 * x) - 1 = (x ^ 3 - 3 * x + 2) / (3 * x) := by
          field_simp
          ring
        rw [h4]
        have h5 : x ^ 3 - 3 * x + 2 ≥ 0 := by
          nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2)]
        have h6 : 3 * x > 0 := by linarith
        apply div_nonneg
        linarith
        all_goals linarith
      linarith
    linarith [hfx, h2]