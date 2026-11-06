import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem inequalities_145246 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3/2 ≤ x/(y+z) + y/(z+x) + z/(x+y) := by
  have h1 : 0 < y + z := by linarith
  have h2 : 0 < z + x := by linarith
  have h3 : 0 < x + y := by linarith

  have h4 : 0 < y + z := h1
  have h5 : 0 < z + x := h2
  have h6 : 0 < x + y := h3

  have h5 : (y + z) * (z + x) * (x + y) > 0 := by positivity

  have h6 : x/(y+z) + y/(z+x) + z/(x+y) - 3/2 ≥ 0 := by

    have h7 : x/(y+z) + y/(z+x) + z/(x+y) - 3/2 =
        (x*(z+x)*(x+y) + y*(y+z)*(x+y) + z*(y+z)*(z+x) - 3/2*(y+z)*(z+x)*(x+y)) / ((y+z)*(z+x)*(x+y)) := by
      field_simp [h1, h2, h3]
      ring

    rw [h7]

    have h8 : x*(z+x)*(x+y) + y*(y+z)*(x+y) + z*(y+z)*(z+x) - 3/2*(y+z)*(z+x)*(x+y) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]

    have h9 : (y+z)*(z+x)*(x+y) > 0 := by positivity

    apply div_nonneg h8 (by positivity)

  linarith