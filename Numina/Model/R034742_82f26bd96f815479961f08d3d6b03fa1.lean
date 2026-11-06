import Mathlib

theorem algebra_96380 {s : Set ℚ} (hs : s = {1/3, 2/5, 1, 5, 1986}):
    IsGreatest ((fun x ↦ 1 / x) '' s) (1 / (1/3)) := by
  rw [hs]
  constructor
  · -- Show that 1/(1/3) is indeed in the image set
    simp
  · -- Show that 1/(1/3) is the greatest element in the image set
    intro y hy
    simp [hs] at hy
    rcases hy with (rfl | rfl | rfl | rfl | rfl)
    all_goals norm_num