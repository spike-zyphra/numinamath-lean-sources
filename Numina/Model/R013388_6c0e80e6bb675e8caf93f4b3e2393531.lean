import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_12383 {f : ℝ → ℝ} (hf : ∀ x > 0, f x - 2 * x * f (1 / x) + 3 * x ^ 2 = 0) :
    IsLeast (Set.image f (Set.Ioi 0)) 3 := by

  have h1 : ∀ x > 0, f x = x^2 + 2 / x := by
    intro x hx
    have eq1 := hf x hx
    have eq2 := hf (1 / x) (by positivity)
    field_simp at eq1 eq2 ⊢
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos (show (1 / x : ℝ) > 0 by positivity), sq_nonneg (x - 1)]

  have h2 : 3 ∈ Set.image f (Set.Ioi 0) := by
    use 1
    constructor
    · norm_num
    · -- Show that f 1 = 3
      specialize h1 1 (by norm_num)
      norm_num at h1 ⊢
      linarith

  have h3 : ∀ y, y ∈ Set.image f (Set.Ioi 0) → 3 ≤ y := by
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : x > 0 := hx
    have hx2 : f x = x ^ 2 + 2 / x := h1 x hx1
    have hx3 : x ^ 2 + 2 / x ≥ 3 := by
      have h4 : x ^ 2 + 2 / x - 3 ≥ 0 := by
        have h5 : x ^ 2 + 2 / x - 3 = (x ^ 3 + 2 - 3 * x) / x := by
          field_simp
          ring
        rw [h5] at *
        apply div_nonneg
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 2), mul_pos hx (show 0 < x from by linarith)]
        all_goals linarith
      linarith

    have eq1 : f x = y := by linarith [hfx]
    have eq2 : f x = x ^ 2 + 2 / x := h1 x hx1
    have eq3 : y = x ^ 2 + 2 / x := by
      linarith [eq1, eq2]
    linarith [eq3, hx3]

  constructor
  · exact h2
  · -- Show 3 is minimal
    intro y hy
    have hx := h3 y hy
    linarith