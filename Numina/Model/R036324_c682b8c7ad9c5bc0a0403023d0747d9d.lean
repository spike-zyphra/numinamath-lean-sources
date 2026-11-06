import Mathlib

open Pointwise
theorem number_theory_97338 (s u : Set ℚ) (hu : u={0.12345}) (hs : s={0.8, 0.07, 0.006, 0.0005, 0.00004}):
IsGreatest (s + u) (0.92345 : ℚ) := by
  constructor
  · -- Show 0.92345 is in the sumset
    rw [hs, hu]
    simp
    <;> norm_num
  · -- Show that 0.92345 is greatest
    intro r hr
    rw [hs, hu] at hr
    simp at hr
    rcases hr with (hr | hr | hr | hr | hr)
    all_goals
      norm_num at hr ⊢
      nlinarith