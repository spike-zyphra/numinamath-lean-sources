import Mathlib

/-Suppose that $x$ and $y$ are real numbers satisfying  \begin{align*}
4y - 4x^2 &= 1 \\
4x - 4y^2 &= 1.
\end{align*} What is $\dfrac{1}{x^3 + y^3}$?-/
theorem algebra_19705 {x y : ℝ} (hx : 4 * y - 4 * x ^ 2 = 1) (hy : 4 * x - 4 * y ^ 2 = 1) :
    1 / (x ^ 3 + y ^ 3) = 4 := by
  -- show that 4 * x ^ 2 - 4 * x + 1 + 4 * y ^ 2 - 4 * y + 1 = 0
  have hxy : 4 * x ^ 2 - 4 * x + 1 + 4 * y ^ 2 - 4 * y + 1 = 0 := by
    calc
      4 * x ^ 2 - 4 * x + 1 + 4 * y ^ 2 - 4 * y + 1 = -(4 * y - 4 * x ^ 2) - (4 * x - 4 * y ^ 2) + 1 + 1 := by ring_nf
      _ = 0 := by rw [hx, hy]; norm_num
  -- show that (2 * x - 1) ^ 2 + (2 * y - 1) ^ 2 = 0
  replace hxy : (2 * x - 1) ^ 2 + (2 * y - 1) ^ 2 = 0 := by ring_nf at hxy ⊢; exact hxy
  -- show that 2 * x - 1 = 0 or 2 * y - 1 = 0
  rw [add_eq_zero_iff_of_nonneg (show 0 ≤ (2 * x - 1) ^ 2 by positivity) (show 0 ≤ (2 * y - 1) ^ 2 by positivity)] at hxy
  repeat rw [sq_eq_zero_iff] at hxy
  -- show that x = 1 / 2 and y = 1 / 2
  replace hx : x = 1 / 2 := by linarith only [hxy]
  replace hy : y = 1 / 2 := by linarith only [hxy]
  -- show the answer
  rw [hx, hy]
  norm_num