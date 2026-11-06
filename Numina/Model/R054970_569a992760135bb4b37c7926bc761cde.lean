import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_21639 (f : ℝ → ℝ) (hf : f = λ x => (x^7 + 32 * x^2 + 128) / x^3) :
    IsLeast {y | ∃ x > 0, f x = y} 48 := by
  constructor
  · -- First, prove 48 is in the set
    use 2
    constructor
    · norm_num
    · -- Show f 2 = 48
      rw [hf]
      norm_num
  · -- Prove 48 is the least element
    intro y hy
    rcases hy with ⟨x, hx_pos, hfx⟩
    rw [hf] at hfx
    simp at hfx
    have h1 : x ^ 7 + 32 * x ^ 2 + 128 ≥ 48 * x ^ 3 := by
      nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 - 4), sq_nonneg (x - 2), sq_nonneg (x + 2),
        sq_nonneg (x * x - 4), sq_nonneg (x ^ 3 - 8), sq_nonneg (x ^ 4 - 16),
        mul_pos hx_pos (show 0 < x from by linarith), 
        sq_nonneg (x ^ 2 - 4 * x + 4)]
    have h2 : (x ^ 7 + 32 * x ^ 2 + 128) / x ^ 3 ≥ 48 := by
      have pos1 : x ^ 3 > 0 := by
        positivity
      apply (le_div_iff₀ pos1).mpr
      nlinarith
    linarith [hfx, h2]