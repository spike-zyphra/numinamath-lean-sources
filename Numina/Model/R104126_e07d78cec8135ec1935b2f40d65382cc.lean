import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_198785 : IsGreatest {y | ∃ x : ℝ, y = x / (x ^ 2 + 4)} (1 / 4) := by 
  constructor
  · -- Show that 1/4 is in the set
    use 2
    norm_num
  · -- Show that 1/4 is the greatest in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : x / (x ^ 2 + 4) ≤ 1 / 4 := by
      have h2 : x ^ 2 + 4 ≥ 0 := by nlinarith [sq_nonneg x]
      have h3 : x ^ 2 + 4 > 0 := by positivity
      have h4 : 4 * x ≤ x ^ 2 + 4 := by
        nlinarith [sq_nonneg (x - 2)]
      have h5 : x / (x ^ 2 + 4) ≤ 1 / 4 := by
        apply (div_le_div_iff (by positivity) (by norm_num)).mpr
        linarith
      linarith [h5]
    linarith [hx, h1]