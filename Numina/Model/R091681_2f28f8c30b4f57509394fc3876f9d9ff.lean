import Mathlib

theorem algebra_307359 (x : ℝ) :
    ⌊2 * x⌋ + ⌊3 * x⌋ = 8 * x - 7 / 2 ↔
    x = 13 / 16 ∨ x = 17 / 16 := by
  constructor
  · -- Assume ⌊2 * x⌋ + ⌊3 * x⌋ = 8 * x - 7 / 2, prove x = 13 / 16 ∨ x = 17 / 16
    intro h
    have h1 : (⌊2 * x⌋ + ⌊3 * x⌋ : ℝ) = 8 * x - 7 / 2 := by exact_mod_cast h
    have h2 : ∃ n : ℤ, (n : ℝ) = 8 * x - 7 / 2 ∧ n = ⌊2 * x⌋ + ⌊3 * x⌋ := by
      use ⌊2 * x⌋ + ⌊3 * x⌋
      constructor
      · exact_mod_cast h
      · rfl
    rcases h2 with ⟨n, hn1, hn2⟩
    have hx : x = (2 * (n : ℝ) + 7) / 16 := by
      nlinarith
    have h3 : n ≤ 5 := by
      have h_floor_le : (⌊2 * x⌋ : ℝ) ≤ 2 * x := by exact Int.floor_le (2 * x)
      have h_floor_le2 : (⌊3 * x⌋ : ℝ) ≤ 3 * x := by exact Int.floor_le (3 * x)
      have h_le : (n : ℝ) ≤ 5 * x := by 
        have : (n : ℝ) = (⌊2 * x⌋ + ⌊3 * x⌋ : ℝ) := by simp [hn2]
        rw [this]
        linarith [h_floor_le, h_floor_le2]
      rw [hx] at h_le
      by_contra h
      push_neg at h
      have h6 : n ≥ 6 := by omega
      have h7 : (n : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h6
      linarith
    have h4 : n ≥ 1 := by
      have h_floor_lt : 2 * x < (⌊2 * x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (2 * x)
      have h3x_lt : 3 * x < (⌊3 * x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (3 * x)
      have h2x_lt : 2 * x < (⌊2 * x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (2 * x)
      have h3x_lt : 3 * x < (⌊3 * x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one (3 * x)
      have h_lt : 5 * x < (n + 2 : ℝ) := by
        have h1 : (⌊2 * x⌋ + ⌊3 * x⌋ + 2 : ℝ) = (n + 2 : ℝ) := by
          simp [hn2]
        have h2 : (⌊2 * x⌋ + 1 : ℝ) + (⌊3 * x⌋ + 1 : ℝ) = (⌊2 * x⌋ + ⌊3 * x⌋ + 2 : ℝ) := by ring
        linarith [h1, h2x_lt, h3x_lt]
      rw [hx] at h_lt
      by_contra h
      push_neg at h
      have h6 : n ≤ 0 := by omega
      have h7 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h6
      nlinarith
    have h5 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases h5 with (r | r | r | r | r)
    · -- n = 1
      have hx1 : x = (2 * (1 : ℤ) + 7) / 16 := by
        rw [show (n : ℝ) = (1 : ℝ) by exact_mod_cast r] at hx
        linarith
      norm_num [hx1, r] at h1 hn1 ⊢
      all_goals omega
    · -- n = 2
      have hx2 : x = (2 * (2 : ℤ) + 7) / 16 := by
        rw [show (n : ℝ) = (2 : ℝ) by exact_mod_cast r] at hx
        linarith
      norm_num [hx2, r] at h1 hn1 ⊢
      all_goals omega
    · -- n = 3
      have hx3 : x = (2 * (3 : ℤ) + 7) / 16 := by
        rw [show (n : ℝ) = (3 : ℝ) by exact_mod_cast r] at hx
        linarith
      have h8 : x = (13 / 16 : ℝ) := by
        norm_num [hx3]
      left
      exact h8
    · -- n = 4
      have hx4 : x = (2 * (4 : ℤ) + 7) / 16 := by
        rw [show (n : ℝ) = (4 : ℝ) by exact_mod_cast r] at hx
        linarith
      norm_num [hx4, r] at h1 hn1 ⊢
      all_goals omega
    · -- n = 5
      have hx5 : x = (2 * (5 : ℤ) + 7) / 16 := by
        rw [show (n : ℝ) = (5 : ℝ) by exact_mod_cast r] at hx
        linarith
      have h9 : x = (17 / 16 : ℝ) := by
        norm_num [hx5]
      right
      exact h9
  · -- Assume x = 13/16 or 17/16 prove ⌊2 * x⌋ + ⌊3 * x⌋ = 8 * x - 7 / 2
    rintro (h | h)
    · -- x = 13/16
      rw [h]
      norm_num
    · -- x = 17/16
      rw [h]
      norm_num