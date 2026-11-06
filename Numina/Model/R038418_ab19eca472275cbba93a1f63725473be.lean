import Mathlib

theorem algebra_297880 (x : ℝ) :
    ⌊2 * x⌋ + ⌊3 * x⌋ = 9 * x - 7 / 4 ↔
    x = -1 / 36 ∨ x = 7 / 36 := by
  constructor
  · -- Assume ⌊2 * x⌋ + ⌊3 * x⌋ = 9 * x - 7 / 4, prove x = -1 / 36 ∨ x = 7 / 36
    intro h_eq
    have h1 : (⌊2 * x⌋ + ⌊3 * x⌋ : ℝ) = 9 * x - 7 / 4 := by
      exact_mod_cast h_eq
    let k := ⌊2 * x⌋ + ⌊3 * x⌋
    have hk1 : (k : ℝ) = 9 * x - 7 / 4 := by
      exact_mod_cast h_eq
    -- Solving for x: x = (4k + 7)/36
    have h2 : x = (4 * (k : ℝ) + 7) / 36 := by
      linarith
    have h3 : (k : ℝ) = (⌊2 * x⌋ : ℝ) + (⌊3 * x⌋ : ℝ) := by
      exact_mod_cast rfl
    have h4 : (⌊2 * x⌋ : ℝ) ≤ 2 * x := by 
      exact_mod_cast (Int.floor_le (2 * x))
    have h5 : 2 * x < (⌊2 * x⌋ + 1 : ℝ) := by 
      exact_mod_cast (Int.lt_floor_add_one (2 * x))
    have h6 : (⌊3 * x⌋ : ℝ) ≤ 3 * x := by 
      exact_mod_cast (Int.floor_le (3 * x))
    have h7 : 3 * x < (⌊3 * x⌋ + 1 : ℝ) := by 
      exact_mod_cast (Int.lt_floor_add_one (3 * x))
    have h8 : k ≤ 2 := by
      by_contra h
      push_neg at h
      have h9 : k ≥ 3 := by omega
      have hk2 : (k : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h9
      nlinarith [h2, h4, h6, hk1, hk2]
    have h9 : k ≥ -2 := by
      by_contra h
      push_neg at h
      have h10 : k ≤ -3 := by omega
      have hk2 : (k : ℝ) ≤ (-3 : ℝ) := by exact_mod_cast h10
      nlinarith [h2, h4, h6, hk1, hk2]
    have h10 : k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ k = 2 := by 
      omega
    rcases h10 with (h | h | h | h | h)
    · -- k = -2
      have hk2 : (k : ℝ) = -2 := by exact_mod_cast h
      have hx1 : x = (-1 : ℝ)/36 := by
        linarith [h2, hk2]
      left
      exact hx1
    · -- k = -1
      have hk2 : (k : ℝ) = -1 := by exact_mod_cast h
      have hx1 : x = (1 : ℝ)/12 := by
        linarith [h2, hk2]
      exfalso
      norm_num [hx1] at h_eq
      all_goals norm_num [Int.floor_eq_iff] at h_eq ⊢
      all_goals omega
    · -- k = 0
      have hk2 : (k : ℝ) = 0 := by exact_mod_cast h
      have hx1 : x = (7 : ℝ)/36 := by
        linarith [h2, hk2]
      right
      exact hx1
    · -- k = 1
      have hk2 : (k : ℝ) = 1 := by exact_mod_cast h
      have hx1 : x = (11 : ℝ)/36 := by
        linarith [h2, hk2]
      exfalso
      norm_num [hx1] at h_eq
      all_goals norm_num [Int.floor_eq_iff] at h_eq ⊢
      all_goals omega
    · -- k = 2
      have hk2 : (k : ℝ) = 2 := by exact_mod_cast h
      have hx1 : x = (5 : ℝ)/12 := by
        linarith [h2, hk2]
      exfalso
      norm_num [hx1] at h_eq
      all_goals norm_num [Int.floor_eq_iff] at h_eq ⊢
      all_goals omega
  · -- Assume x = -1/36 ∨ x = 7/36, prove ⌊2 * x⌋ + ⌊3 * x⌋ = 9 * x - 7 / 4
    rintro (h_eq | h_eq)
    · -- x = -1/36
      rw [h_eq]
      norm_num [Int.floor_eq_iff]
      all_goals norm_num
    · -- x = 7/36
      rw [h_eq]
      norm_num [Int.floor_eq_iff]
      all_goals norm_num