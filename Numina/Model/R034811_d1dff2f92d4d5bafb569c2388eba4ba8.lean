import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_261657 {V : ℝ → ℝ}
  (hV : ∀ x, V x = (5 * x ^ 4 - 4 * x ^ 2 + 5) / (x ^ 4 + 1)) :
  (∀ x, V x ≥ 3) ∧ IsGreatest (range V) 5 := by
  constructor
  · -- Prove that ∀ x, V x ≥ 3
    intro x
    have h1 : V x = (5 * x ^ 4 - 4 * x ^ 2 + 5) / (x ^ 4 + 1) := hV x
    rw [h1]
    have h2 : (5 * x ^ 4 - 4 * x ^ 2 + 5) / (x ^ 4 + 1) ≥ 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2), sq_nonneg (x ^ 4 - 1)]
    exact h2
  · -- Show that 5 is greatest element in the range
    constructor
    · -- Show that 5 is in the range
      use 0
      rw [hV]
      norm_num
    · -- Show that 5 is greatest
      intro y
      rintro ⟨x, hx⟩
      rw [hV x] at hx
      have h2 : (5 * x ^ 4 - 4 * x ^ 2 + 5) / (x ^ 4 + 1) ≤ 5 := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 4 - 1)]
      linarith [h2, hx]