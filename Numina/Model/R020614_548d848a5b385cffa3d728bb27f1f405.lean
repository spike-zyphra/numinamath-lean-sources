import Mathlib

theorem algebra_274047 (x : ℝ) :
    x * ⌊x⌋ - 5 * x + 7 = 0 ↔ x = 7 / 4 ∨ x = 7 / 3 ∨ x = 7 / 2 := by
  constructor
  · -- If h then x equals expressions
    intro h
    have h1 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)
    have h6 : ⌊x⌋ = 1 ∨ ⌊x⌋ = 2 ∨ ⌊x⌋ = 3 := by
      have h7 : ⌊x⌋ ≤ 3 := by
        by_contra h
        push_neg at h
        have h8 : ⌊x⌋ ≥ 4 := by omega
        have h9 : (⌊x⌋ : ℝ) ≥ (4 : ℝ) := by exact_mod_cast h8
        nlinarith [h1, h2, show (⌊x⌋ : ℝ) ≥ (4 : ℝ) from h9]
      have h10 : ⌊x⌋ ≥ 1 := by
        by_contra h
        push_neg at h
        have h11 : ⌊x⌋ ≤ 0 := by omega
        have h12 : (⌊x⌋ : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h11
        nlinarith [show (⌊x⌋ : ℝ) ≤ (0 : ℝ) from h12, h1, h2]
      omega
    rcases h6 with (h10 | h11 | h12)
    · -- Case ⌊x⌋ = 1
      have h13 : (⌊x⌋ : ℝ) = (1 : ℝ) := by exact_mod_cast h10
      have hx1 : x = (7 / 4 : ℝ) := by
        simp [h13] at h
        linarith
      left
      linarith
    · -- Case ⌊x⌋ = 2
      have h14 : (⌊x⌋ : ℝ) = (2 : ℝ) := by exact_mod_cast h11
      have hx2 : x = (7 / 3 : ℝ) := by
        simp [h14] at h
        linarith
      right
      left
      linarith
    · -- Case ⌊x⌋ = 3
      have h15 : (⌊x⌋ : ℝ) = (3 : ℝ) := by exact_mod_cast h12
      have hx3 : x = (7 / 2 : ℝ) := by
        simp [h15] at h
        linarith
      right
      right
      linarith
  · -- If x equals expressions then equation holds
    rintro (h | h | h)
    · -- Case x = 7/4
      rw [h]
      norm_num [Int.floor_eq_iff]
    · -- Case x = 7/3
      rw [h]
      norm_num [Int.floor_eq_iff]
    · -- Case x = 7/2
      rw [h]
      norm_num [Int.floor_eq_iff]