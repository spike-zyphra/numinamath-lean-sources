import Mathlib

/- Carla spent two-fifths of her savings on a bracelet and had $\$ 9$ left over. How many dollars did Carla's bracelet cost? -/
theorem algebra_20372 {x : ℝ} (h : (1 - 2 / 5) * x = 9) : 2 / 5 * x = 6 := by
  linarith