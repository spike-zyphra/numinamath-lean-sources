import Mathlib

theorem number_theory_97155 (s: Set ℚ) (hs: s = {0.99, 0.9099, 0.9, 0.909, 0.9009}) : 
IsGreatest s (0.99) := by
  unfold IsGreatest
  constructor
  · -- Show that 0.99 ∈ s
    rw [hs]
    simp
  · -- Show that 0.99 is the greatest in s
    intro x hx
    rw [hs] at hx
    simp at hx
    rcases hx with (rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num at *