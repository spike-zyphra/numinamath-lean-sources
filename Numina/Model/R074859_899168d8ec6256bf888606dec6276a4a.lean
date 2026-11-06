import Mathlib

theorem algebra_9311
  (a : ℕ → ℝ)
  (ha1 : a 1 = 2)
  (han : ∀ n > 0, a (n + 1) - 2 * a n = 2 ^ (n + 1))
  : IsLeast {n | 0 < n ∧ a n > 10} 3 := by
  have ha2 : a 2 = 8 := by
    have eq1 := han 1 (by norm_num)
    norm_num at eq1 
    rw [ha1] at eq1 
    linarith 
  have ha3 : a 3 = 24 := by
    have eq2 := han 2 (by norm_num)
    norm_num at eq2 
    rw [ha2] at eq2 
    linarith 
  constructor
  · -- Show that 3 belongs to the set {n | 0 < n ∧ a n > 10}
    constructor
    · -- Show that 3 is positive
      norm_num 
    · -- Show that a 3 > 10
      linarith [ha3] 
  · -- Show that 3 is the smallest element in the set
    intro n hn
    have h_pos : 0 < n := hn.1 
    have h_lt : a n > 10 := hn.2 
    by_contra h 
    push_neg at h 
    have h2 : n = 1 ∨ n = 2 := by omega 
    rcases h2 with (rfl | rfl)
    · -- Case n = 1
      have h_a1 : a 1 = 2 := ha1
      linarith [h_a1, h_lt] 
    · -- Case n = 2
      have h_a2 : a 2 = 8 := ha2 
      linarith [h_a2, h_lt]