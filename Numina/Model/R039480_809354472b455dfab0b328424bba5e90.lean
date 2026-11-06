import Mathlib

theorem number_theory_97660 (s : Set ℕ) (hs: s = {m : ℕ | (m + 23) % 6 = 0}) :
IsLeast (s) (1) := by
  constructor
  · -- Show that 1 is in the set
    rw [hs]
    norm_num
  · -- Show that for all m in s, 1 ≤ m
    intro m hm
    rw [hs] at hm
    simp at hm
    omega