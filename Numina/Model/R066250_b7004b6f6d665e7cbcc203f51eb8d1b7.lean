import Mathlib

theorem algebra_196358 (x : ℝ) (hx : x = 0.8) :
    IsLeast {n | (1 - x ^ n) ≥ 1 / 3} 2 := by
  constructor
  · -- Show that 2 is in the set
    rw [Set.mem_setOf_eq]
    rw [hx]
    norm_num
  · -- Show that 2 is the smallest element in the set
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    rw [hx] at hn
    by_contra h
    push_neg at h
    have h1 : n < 2 := by linarith
    have h2 : n = 0 ∨ n = 1 := by omega
    rcases h2 with (r | r)
    · -- Case n = 0
      rw [r] at hn
      norm_num at hn
      all_goals linarith
    · -- Case n = 1
      rw [r] at hn
      norm_num at hn
      all_goals linarith