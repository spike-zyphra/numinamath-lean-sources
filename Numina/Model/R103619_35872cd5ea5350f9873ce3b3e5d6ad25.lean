import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_104835 (f : ℝ → ℝ) (hf : f = λ x => x^2 / (x - 9)) :
    IsLeast {y | ∃ x, x > 9 ∧ f x = y} 36 := by
  constructor
  · -- Show there exists x > 9 such that f x = 36.
    use 18
    constructor
    · -- Show 18 > 9.
      norm_num
    · -- Show f 18 = 36.
      rw [hf]
      norm_num
  · -- Show that 36 is the least value in the set.
    intro y hy
    rcases hy with ⟨x, hx, heq⟩
    -- We have that x > 9 and f x = y, need to show 36 ≤ y.
    rw [hf] at heq
    have h1 : x ^ 2 / (x - 9) = y := by
      simpa using heq
    have hx1 : x - 9 > 0 := by linarith
    have h2 : x ^ 2 / (x - 9) ≥ 36 := by
      have h3 : x ^ 2 ≥ 36 * (x - 9) := by
        nlinarith [sq_nonneg (x - 18)]
      have h5 : x - 9 > 0 := by linarith
      apply (le_div_iff₀ h5).mpr
      nlinarith [sq_nonneg (x - 18)]
    have h3 : x ^ 2 / (x - 9) ≥ 36 := h2
    linarith [h1, h3]