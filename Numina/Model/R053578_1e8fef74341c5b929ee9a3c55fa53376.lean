import Mathlib

theorem algebra_14134 (r : ℝ) : ⌊r⌋ + r = 12.2 ↔ r = 6.2 := by
  constructor
  · -- Assume ⌊r⌋ + r = 12.2, prove r = 6.2
    intro h
    let n := ⌊r⌋
    have h1 : (n : ℝ) + r = 12.2 := by 
      exact_mod_cast h 
    have h2 : (n : ℝ) ≤ r := by
      apply Int.floor_le 
    have h3 : r < ((n : ℝ) + 1 : ℝ) := by 
      apply Int.lt_floor_add_one 
    have h4 : r = 12.2 - (n : ℝ) := by 
      linarith 
    rw [h4] at h2 h3 
    have h5 : (n : ℝ) ≤ 6.1 := by 
      nlinarith 
    have h6 : (5.6 : ℝ) < (n : ℝ) := by 
      nlinarith 
    have hn1 : n = 6 := by 
      have h7 : n ≤ 6 := by 
        by_contra h8 
        push_neg at h8 
        have h9 : n ≥ 7 := by omega 
        have h10 : (n : ℝ) ≥ (7 : ℝ) := by exact_mod_cast h9 
        linarith 
      have h7 : n ≥ 6 := by 
        by_contra h8 
        push_neg at h8 
        have h9 : n ≤ 5 := by omega 
        have h10 : (n : ℝ) ≤ (5 : ℝ) := by exact_mod_cast h9 
        linarith 
      omega 
    have hr : r = 6.2 := by 
      rw [show (n : ℝ) = (6 : ℝ) by exact_mod_cast hn1] at h1 
      linarith 
    linarith 
  · -- Assume r = 6.2, prove ⌊r⌋ + r = 12.2
    intro h 
    rw [h] 
    norm_num 
    all_goals norm_num 
    all_goals try { simp }
    all_goals norm_num 
    all_goals try { simp }