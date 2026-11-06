import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_190803 :
  IsLeast {x | ∃ t : ℝ, x = ∑ i ∈ Finset.range 53, (t - (i * 2))^2} 49608 := by
  constructor
  · -- Show that 49608 is in the set.
    use 52
    norm_num [Finset.sum_range_succ]
  · -- Show that for any s in the set, 49608 ≤ s
    intro s
    rintro ⟨t, ht⟩
    have h1 : ∑ i in Finset.range 53, (t - (i * 2))^2 ≥ 49608 := by
      have h2 : ∀ t : ℝ, ∑ i in Finset.range 53, (t - (i * 2))^2 = 53 * (t - 52) ^ 2 + 49608 := by
        intro t
        simp [Finset.sum_range_succ]
        ring_nf
      have h3 : ∑ i in Finset.range 53, (t - (i * 2)) ^ 2 = 53 * (t - 52) ^ 2 + 49608 := h2 t
      rw [h3]
      have h4 : 53 * (t - 52) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (t - 52)]
      linarith
    linarith [ht, h1]