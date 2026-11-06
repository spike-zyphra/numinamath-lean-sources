import Mathlib

/- If $x$ and $y$ are both positive numbers, and $xy + x + y = \frac{7}{9}$, then the maximum value of $-x^2y^2 + xy$ is ___        ___. -/
theorem algebra_3570 : IsGreatest {z:ℝ | ∃(x y:ℝ), 0 < x ∧ 0 < y ∧ x * y + x + y = 7 / 9 ∧ z = -x ^ 2 * y ^ 2 + x * y} (8 / 81) := by 
  constructor
  · -- First, show that 8/81 is in the set, using x = y = 1/3
    use 1 / 3, 1 / 3
    norm_num
  · -- Show that 8/81 is the greatest
    intro z hz
    rcases hz with ⟨x, y, hx, hy, h1, h2⟩
    nlinarith [sq_nonneg (x * y - 1 / 9), sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), sq_nonneg (x * y), sq_nonneg (x + y - 2 / 3), sq_nonneg (x * 3 - 1), sq_nonneg (y * 3 - 1), mul_pos hx hy, h1]