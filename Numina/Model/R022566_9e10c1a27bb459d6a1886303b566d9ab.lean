import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_6645 (f : ℝ → ℝ) (hf : f = λ x => 1 / (x^2 - 6 * x + 19)) :
    IsGreatest {y | ∃ x, x ≥ 5 ∧ f x = y} (1 / 14) := by
  constructor
  · -- Show that 1/14 is in the set.
    use 5
    constructor
    · norm_num -- Show 5 ≥ 5
    · -- Show f 5 = 1 / 14
      rw [hf]
      norm_num
  · -- Show that 1/14 is the greatest
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    have h_eq : 1 / (x^2 - 6 * x + 19) = y := by
      simpa using hfx
    have h1 : x ^ 2 - 6 * x + 19 ≥ 14 := by
      nlinarith [sq_nonneg (x - 5), sq_nonneg (x - 3)]
    have h2 : 1 / (x^2 - 6 * x + 19) ≤ 1 / (14 : ℝ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      linarith only [h1]
    linarith [h_eq, h2]