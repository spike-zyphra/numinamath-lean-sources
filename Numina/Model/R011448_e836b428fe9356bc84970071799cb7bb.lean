import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_14025 :
  IsGreatest {x | ∃ a b : ℝ, a ∈ Icc 0 2 ∧ b ∈ Icc 0 2 ∧ x = a^2 - a + |b - a|} 4 := by
  constructor
  · -- Show 4 is in the set
    use 2, (0 : ℝ)
    constructor
    · -- Show that 2 ∈ [0, 2]
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show that 0 ∈ [0, 2]
      exact ⟨by norm_num, by norm_num⟩
    · -- Check that the expression equals 4
      norm_num [abs]
  · -- Show 4 is an upper bound
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h_eq⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    by_cases h : b - a ≥ 0
    · -- Case where b ≥ a
      have habs : |b - a| = b - a := by
        rw [abs_of_nonneg]
        linarith
      rw [habs] at h_eq
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 0)]
    · -- Case where b < a
      have habs : |b - a| = a - b := by
        rw [abs_of_neg]
        linarith
        all_goals linarith
      rw [habs] at h_eq
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 0)]