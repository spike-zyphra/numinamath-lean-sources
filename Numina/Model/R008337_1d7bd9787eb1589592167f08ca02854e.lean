import Mathlib

theorem algebra_11765 : IsLeast {n : ℕ | 0 < n ∧ 200 + 12 * n < 100 + 15 * n} 34 := by
  constructor
  · -- Show 34 is in the set 
    constructor
    · -- Show 0 < 34
      norm_num 
    · -- Show 200 + 12 * 34 < 100 + 15 * 34
      norm_num 
  · -- Show that 34 is the least element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_ineq⟩
    by_contra h
    push_neg at h 
    -- Now assume n < 34, so n <= 33 
    have h1 : n ≤ 33 := by linarith
    -- From 200 + 12 * n < 100 + 15 * n and n <= 33 derive a contradiction 
    have h2 : 200 + 12 * n ≥ 100 + 15 * n := by
      omega
    linarith