import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_106035 : IsGreatest {y : ℝ | ∃ x ∈ Icc 0 1, y = abs (8 * x ^ 2 - 2 * x - 3)} (3 + 1 / 8) := by 
  constructor
  · -- Prove that 3 + 1/8 is attainable, by finding an x ∈ [0,1] that gives this value
    use 1 / 8
    constructor
    · -- Show 1/8 ∈ Icc 0 1
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that abs (8 * (1/8) ^ 2 - 2 * (1/8) - 3) = 3 + 1/8
      norm_num [abs_of_nonneg]
      all_goals norm_num
      all_goals linarith
  · -- Prove that for all y in the set, y ≤ 3 + 1/8
    intro y
    rintro ⟨x, hx, rfl⟩
    have h1 : 0 ≤ x := by
      linarith [hx.1]
    have h2 : x ≤ 1 := by
      linarith [hx.2]
    have h3 : - (3 + 1 / 8) ≤ 8 * x ^ 2 - 2 * x - 3 := by
      nlinarith [sq_nonneg (x - 1 / 8)]
    have h4 : 8 * x ^ 2 - 2 * x - 3 ≤ 3 + 1 / 8 := by
      nlinarith [sq_nonneg (x - 1 / 8)]
    apply abs_le.mpr
    constructor <;> linarith