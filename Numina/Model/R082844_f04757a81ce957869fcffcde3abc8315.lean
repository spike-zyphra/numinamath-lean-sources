import Mathlib

theorem algebra_132295 {f : ℝ → ℝ → ℝ → ℝ}
    (hf : f = fun x y z => x^3 * (y - z) + y^3 * (z - x) + z^3 * (x - y)) :
    f = fun x y z => -(x - y) * (y - z) * (z - x) * (x + y + z) := by
  funext x y z
  simp [hf]
  ring