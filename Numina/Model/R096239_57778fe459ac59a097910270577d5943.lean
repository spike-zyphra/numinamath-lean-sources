import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_169560 (f : ℝ → ℝ) (hf : f = λ x => (4 * x ^ 2 + 8 * x + 13) / (6 * (1 + x))) :
    IsLeast {y | ∃ x, x > 0 ∧ f x = y} 2 := by 
  constructor
  · -- Show 2 is in the set 
    use 1 / 2
    constructor
    · norm_num
    · -- Verify f(1/2) = 2
      rw [hf]
      norm_num
  · -- Show 2 is a lower bound 
    intro y hy
    rcases hy with ⟨x, hx_pos, hfx_eq⟩
    rw [hf] at hfx_eq
    have eq1 : (4 * x ^ 2 + 8 * x + 13) / (6 * (1 + x)) = y := by 
      simpa using hfx_eq
    have h4 : (4 * x ^ 2 + 8 * x + 13) / (6 * (1 + x)) ≥ 2 := by
      have h5 : 6 * (1 + x) > 0 := by
        nlinarith 
      apply (le_div_iff₀' h5).mpr 
      -- Now need to show 4x^2 + 8x + 13 ≥ 12(1 + x)
      have h2 : (2 * (x + 1) - 3) ^ 2 ≥ 0 := sq_nonneg (2 * (x + 1) - 3)
      have h3 : 4 * x^2 + 8 * x + 13 ≥ 12 * (1 + x) := by
        nlinarith [sq_nonneg (x + 1), h2]
      linarith 
    linarith [eq1, h4]