import Mathlib

/- A TV screen measures 24 by 16 inches. If each dimension is increased by 20$\%$, by what percent is the area increased? -/
theorem algebra_19988 {x y : ℝ} (hx : x = 24) (hy : y = 16) :
    (x * 1.2 * y * 1.2) / (x * y) - 1 = 44 / 100 := by
  rw [hx, hy]
  ring