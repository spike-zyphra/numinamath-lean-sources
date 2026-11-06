import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_22051 : IsLeast {y : ℝ | ∃ x > 0, y = (x + 5) * (x + 2) / (x + 1)} 9 := by
  constructor
  · -- Show 9 is in the set
    use 1
    norm_num
  · -- Show no value smaller than 9 is in the set
    intro y hy
    rcases hy with ⟨x, hx, heq⟩
    have h1 : x > 0 := hx
    have h2 : (x + 1) > 0 := by linarith
    have h3 : (x + 5) * (x + 2) / (x + 1) ≥ 9 := by
      have h4 : (x + 5) * (x + 2) ≥ 9 * (x + 1) := by
        nlinarith [sq_nonneg (x - 1)]
      have h5 : (x + 5) * (x + 2) / (x + 1) ≥ 9 := by
        apply (le_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith [heq, h3]