import Mathlib

theorem algebra_9386: IsLeast { s:ℝ | ∃(x y z:ℝ), (s = 2*x^2+3*y^2+z^2 ∧  x+y+z=(2:ℝ))} ((24:ℝ) / 11) := by
  constructor
  · -- Show that 24/11 is on the set
    use (6 / 11), (4 / 11), (12 / 11)
    norm_num
  · -- Show that any s on the set is ≥ 24/11
    intro s h
    rcases h with ⟨x, y, z, h1, h2⟩
    have h3 : z = 2 - x - y := by linarith
    rw [h3] at h1
    nlinarith [sq_nonneg (x - 6 / 11), sq_nonneg (y - 4 / 11), sq_nonneg ((2 - x - y) - 12 / 11), 
        sq_nonneg (6 * x + 2 * y - 4), sq_nonneg (2 * x + 8 * y - 4)]