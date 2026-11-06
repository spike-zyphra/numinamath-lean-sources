import Mathlib

theorem algebra_319775 (x : ℝ) :
  ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5 ↔
  x = 7 / 15 ∨ x = 4 / 5 := by
  constructor
  · -- Forward direction: if ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5 then x = 7 / 15 ∨ x = 4 / 5
    intro h
    let n := ⌊(5 + 6 * x) / 8⌋
    have hn1 : (n : ℝ) = (15 * x - 7) / 5 := by
      exact_mod_cast h
    have hn2 : n ≤ (5 + 6 * x) / 8 := by 
      exact Int.floor_le ( (5 + 6 * x) / 8 )
    have hn3 : (5 + 6 * x) / 8 < n + 1 := by 
      exact Int.lt_floor_add_one ( (5 + 6 * x) / 8 )
    have h2 : n = 0 ∨ n = 1 := by 
      have h21 : n ≤ 1 := by 
        by_contra h22
        push_neg at h22
        have h23 : n ≥ 2 := by omega
        have h24 : (n : ℝ) ≥ (2 : ℝ) := by exact_mod_cast h23
        nlinarith [show (n : ℝ) = (15 * x - 7) / 5 from by exact_mod_cast h, hn2, hn3]
      have h22 : n ≥ 0 := by 
        by_contra h22
        push_neg at h22
        have h23 : n ≤ -1 := by omega
        have h24 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h23
        nlinarith [show (n : ℝ) = (15 * x - 7) / 5 from by exact_mod_cast h, hn2, hn3]
      interval_cases n <;> tauto
    rcases h2 with hk | hk
    · 
      have hk0 : (n : ℝ) = (0 : ℝ) := by exact_mod_cast hk
      have hx1 : x = 7 / 15 := by
        linarith [hn1, hk0]
      left
      linarith
    · 
      have hk1 : (n : ℝ) = (1 : ℝ) := by exact_mod_cast hk
      have hx2 : x = 4 / 5 := by
        linarith [hn1, hk1]
      right
      linarith
  · -- Backward direction: if x = 7 / 15 ∨ x = 4 / 5 then ⌊(5 + 6 * x) / 8⌋ = (15 * x - 7) / 5
    rintro (h | h)
    · 
      rw [h]
      norm_num [Int.floor_eq_iff]
    · 
      rw [h]
      norm_num [Int.floor_eq_iff]