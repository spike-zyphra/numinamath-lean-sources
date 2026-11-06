import Mathlib

theorem algebra_193288 (x : ℝ) :
    ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5 ↔ x = 7 / 15 ∨ x = 4 / 5 := by
  constructor
  · -- Assume `⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5`, prove `x = 7 / 15 ∨ x = 4 / 5`.
    intro h
    let n := ⌊(5 + 6 * x) / 8⌋
    have hn1 : (n : ℝ) = (15 * x - 7) / 5 := by
      exact_mod_cast h
    have h3 : (n : ℝ) ≤ (5 + 6 * x) / 8 := by
      exact_mod_cast (Int.floor_le ( (5 + 6 * x) / 8 ) )
    have h4 : (5 + 6 * x) / 8 < (n + 1 : ℝ) := by
      exact_mod_cast (Int.lt_floor_add_one ( (5 + 6 * x) / 8 ) )
    have h5 : (x : ℝ) = (5 * (n : ℝ) + 7) / 15 := by
      linarith [hn1]
    have h6 : n ≥ 0 := by
      by_contra h7
      push_neg at h7
      have h8 : n ≤ -1 := by omega
      have h9 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h8
      nlinarith [h5, h4]
    have h7 : n ≤ 1 := by
      by_contra h8
      push_neg at h8
      have  h8 : n ≥ 2 := by omega
      have h9 : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h8
      nlinarith [h5, h3]
    have h8 : n = 0 ∨ n = 1 := by omega
    rcases h8 with (h8 | h8)
    · -- n = 0
      have hn2 : (n : ℝ) = 0 := by exact_mod_cast h8
      left
      linarith [hn1, hn2]
    · -- n = 1
      have hn2 : (n : ℝ) = 1 := by exact_mod_cast h8
      right
      linarith [hn1, hn2]
  · -- Assume `x = 7 / 15 ∨ x = 4 / 5`, prove `⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5`.
    rintro (h1 | h2)
    · -- x = 7/15
      rw [h1]
      norm_num [Int.floor_eq_iff]
    · -- x = 4/5
      rw [h2]
      norm_num [Int.floor_eq_iff]