import Mathlib

theorem algebra_236882 (x : ℝ) :
    ⌊(9 * x - 4) / 6⌋ = (12 * x + 7) / 4 ↔ x = -9 / 4 ∨ x = -23 / 12 := by
  constructor
  · -- Forward direction: if the equation holds, prove x is one of the two solutions
    intro h
    let n := ⌊(9 * x - 4) / 6⌋
    have h1 : (n : ℝ) = (12 * x + 7) / 4 := by
      exact_mod_cast h
    have h2 : (n : ℝ) ≤ (9 * x - 4) / 6 := by
      exact_mod_cast (Int.floor_le ((9 * x - 4) / 6))
    have h3 : (9 * x - 4) / 6 < (n + 1 : ℝ) := by
      exact_mod_cast (Int.lt_floor_add_one ((9 * x - 4) / 6))
    have h4 : n = -5 ∨ n = -4 := by
      have h5 : n ≤ -4 := by
        by_contra h
        push_neg at h
        have h6 : n ≥ -3 := by
          omega
        have h7 : (n : ℝ) ≥ (-3 : ℝ) := by
          exact_mod_cast h6
        nlinarith [h1, h2, h3, h7]
      have h8 : n ≥ -5 := by
        by_contra h
        push_neg at h
        have h9 : n ≤ -6 := by
          omega
        have h10 : (n : ℝ) ≤ (-6 : ℝ) := by
          exact_mod_cast h9
        nlinarith [h1, h2, h3, h10]
      interval_cases n <;> omega
    rcases h4 with h4 | h4
    · -- Case n = -5
      have h5 : (n : ℝ) = -5 := by
        exact_mod_cast h4
      have h5' : x = -9 / 4 := by
        nlinarith [h1, h4]
      left
      exact h5'
    · -- Case n = -4
      have h5 : (n : ℝ) = -4 := by
        exact_mod_cast h4
      have h5' : x = -23 / 12 := by
        nlinarith [h1, h4]
      right
      exact h5'
  · -- Backward direction: if x is one of the two solutions, then the equation holds
    rintro (h | h)
    · -- Case x = -9/4
      rw [h]
      norm_num [Int.floor_eq_iff]
    · -- Case x = -23/12
      rw [h]
      norm_num [Int.floor_eq_iff]