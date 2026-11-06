import Mathlib

theorem algebra_144500 (line : ℝ → ℝ → Prop)
    (hline : line = fun x y => (3 * x / 2 - y / 3 = 1)) :
    line (2 / 3) 0 ∧ line 0 (-3) := by
  have hx : line (2 / 3) 0 := by 
    rw [hline]
    norm_num
  have hy : line 0 (-3) := by 
    rw [hline]
    norm_num
  exact ⟨hx, hy⟩