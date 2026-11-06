import Mathlib

theorem number_theory_111941 (x : ℝ) :
    x - 1 < ⌊x⌋ ∧ ⌊x⌋ ≤ x ∧
    (⌊2 * x⌋ - 2 * ⌊x⌋ = 0 ∨ ⌊2 * x⌋ - 2 * ⌊x⌋ = 1) := by
  constructor
  · -- Show that x - 1 < ⌊x⌋
    have h3 : x < ⌊x⌋ + 1 := by
      exact Int.lt_floor_add_one x
    linarith
  constructor
  · -- Show that ⌊x⌋ ≤ x
    exact Int.floor_le x
  · -- Show that ⌊2 * x⌋ - 2 * ⌊x⌋ ∈ {0, 1}
    have h1 : ⌊2 * x⌋ = 2 * ⌊x⌋ ∨ ⌊2 * x⌋ = 2 * ⌊x⌋ + 1 := by
      let n := ⌊x⌋
      have h2 : n ≤ x := by
        exact Int.floor_le x
      have h3 : x < (n + 1 : ℝ) := by
        exact Int.lt_floor_add_one x
      have h4 : 2 * (n : ℝ) ≤ 2 * x := by
        nlinarith
      have h5 : 2 * x < 2 * (n + 1 : ℝ) := by
        nlinarith
      by_cases h6 : 2 * x < (2 * (n : ℝ) + 1)
      · -- In this case, since 2n ≤ 2x < 2n + 1, ⌊2x⌋ = 2n
        have h7 : ⌊2 * x⌋ = 2 * n := by
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> nlinarith
        rw [h7]
        simp
      · -- In this case, since 2n + 1 ≤ 2x < 2n + 2, ⌊2x⌋ = 2n + 1
        have h11 : ⌊2 * x⌋ = 2 * n + 1 := by
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> nlinarith
        rw [h11]
        simp
    rcases h1 with h | h
    · -- If ⌊2 * x⌋ = 2 * ⌊x⌋, then the difference is 0
      left
      linarith
    · -- If ⌊2 * x⌋ = 2 * ⌊x⌋ + 1, then the difference is 1
      right
      linarith