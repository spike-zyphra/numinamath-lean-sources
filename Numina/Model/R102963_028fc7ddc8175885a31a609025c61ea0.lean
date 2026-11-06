import Mathlib

theorem algebra_236820 (x : ℝ) : ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5 ↔
    x = 7 / 15 ∨ x = 4 / 5 := by
  constructor
  · -- Assume ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5, prove x = 7 / 15 ∨ x = 4 / 5
    intro h_eq
    have h1 : (⌊(5 + 6 * x) / 8⌋ : ℝ) = (15 * x - 7) / 5 := by exact_mod_cast h_eq
    let k := ⌊(5 + 6 * x) / 8⌋
    have h2 : (k : ℝ) = (15 * x - 7) / 5 := by exact_mod_cast h_eq
    have h3 : (k : ℝ) ≤ (5 + 6 * x) / 8 := by
      exact_mod_cast Int.floor_le ((5 + 6 * x) / 8)
    have h4 : (5 + 6 * x) / 8 < (k + 1 : ℝ) := by
      exact_mod_cast Int.lt_floor_add_one ((5 + 6 * x) / 8)
    have hk1 : k = 0 ∨ k = 1 := by
      have h5 : k ≤ 1 := by
        by_contra h6
        push_neg at h6
        have h6' : k ≥ 2 := by omega
        have h7 : (k : ℝ) ≥ (2 : ℝ) := by
          exact_mod_cast h6'
        nlinarith
      have h8 : k ≥ 0 := by
        by_contra h6
        push_neg at h6
        have h6' : k ≤ -1 := by omega
        have h7 : (k : ℝ) ≤ (-1 : ℝ) := by
          exact_mod_cast h6'
        nlinarith
      omega
    rcases hk1 with hk0 | hk1
    · -- k = 0
      have hk0' : (k : ℝ) = (0 : ℝ) := by exact_mod_cast hk0
      have h10 : (15 * x - 7) / 5 = 0 := by linarith
      have h11 : 15 * x - 7 = 0 := by
        linarith
      have hx : x = 7 / 15 := by
        linarith
      left
      exact hx
    · -- k = 1
      have hk1' : (k : ℝ) = (1 : ℝ) := by exact_mod_cast hk1
      have h12 : (15 * x - 7) / 5 = 1 := by linarith
      have h13 : 15 * x - 7 = 5 := by
        linarith
      have hx : x = 4 / 5 := by
        linarith
      right
      exact hx
  · -- Backward direction
    rintro (h | h)
    · -- Assume x = 7/15
      rw [h]
      norm_num [Int.floor_eq_iff]
    · -- Assume x = 4/5
      rw [h]
      norm_num [Int.floor_eq_iff]