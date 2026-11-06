import Mathlib

theorem algebra_13613 : {r : ℝ | r + ⌊r⌋ = 16.5} = {8.5} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume r + ⌊ r ⌋ = 16.5, prove r = 8.5
    intro h
    let n := ⌊r⌋
    have hn1 : (n : ℝ) ≤ r := by exact_mod_cast (Int.floor_le r)
    have hn2 : r < ((n + 1) : ℝ) := by exact_mod_cast (Int.lt_floor_add_one r)
    have h_eq : r + (n : ℝ) = 16.5 := by
      simpa using h
    have hneq : n = 8 := by
      have : (n : ℝ) ≤ r := by exact_mod_cast (Int.floor_le r)
      have hr : r = (16.5 : ℝ) - (n : ℝ) := by linarith
      rw [hr] at hn1 hn2
      have hn3 : (n : ℝ) ≤ (8.25 : ℝ) := by
        nlinarith
      have hn4 : (n : ℝ) > (7.75 : ℝ) := by
        nlinarith
      have hn5 : n > 7 := by
        by_contra h'
        push_neg at h'
        have : n ≤ 7 := by omega
        have : (n : ℝ) ≤ (7 : ℝ) := by exact_mod_cast this
        nlinarith
      have hn6 : n ≤ 8 := by
        by_contra h'
        push_neg at h'
        have : n ≥ 9 := by omega
        have : (n : ℝ) ≥ (9 : ℝ) := by exact_mod_cast this
        nlinarith
      omega
    have hre : r = 8.5 := by
      rw [show (n : ℝ) = 8 by exact_mod_cast hneq] at h_eq
      linarith
    linarith
  · -- Assume r = 8.5, prove r + ⌊ r ⌋ = 16.5
    intro h
    rw [h]
    norm_num [Int.floor_eq_iff]
    all_goals norm_num