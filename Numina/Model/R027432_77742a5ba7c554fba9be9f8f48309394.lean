import Mathlib

theorem algebra_598225 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (u v w : ℝ) (hu : u = 4 * y * z / ((x + y) * (x + z))) (hv : v = 4 * x * z / ((x + y) * (y + z)))
    (hw : w = 4 * x * y / ((x + z) * (y + z))) :
    u > 0 ∧ v > 0 ∧ w > 0 := by
  constructor
  · -- Prove that u > 0
    rw [hu]
    apply div_pos
    · -- Show that 4 * y * z > 0
      positivity
    · -- Show that (x + y) * (x + z) > 0
      positivity
  constructor
  · -- Prove that v > 0
    rw [hv]
    apply div_pos
    · -- Show that 4 * x * z > 0
      positivity
    · -- Show that (x + y) * (y + z) > 0
      positivity
  · -- Prove that w > 0
    rw [hw]
    apply div_pos
    · -- Show that 4 * x * y > 0
      positivity
    · -- Show that (x + z) * (y + z) > 0
      positivity