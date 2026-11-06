import Mathlib

/- Assume that $x_1,x_2,\ldots,x_7$ are real numbers such that
\[\begin{aligned} x_1+4x_2+9x_3+16x_4+25x_5+36x_6+49x_7 &= 1 \\ 
4x_1+9x_2+16x_3+25x_4+36x_5+49x_6+64x_7 &= 12 \\
9x_1+16x_2+25x_3+36x_4+49x_5+64x_6+81x_7 &= 123. \end{aligned}\]Find the value of $16x_1+25x_2+36x_3+49x_4+64x_5+81x_6+100x_7$. -/
theorem algebra_13601 (x : Fin 7 → ℝ)
    (h₀ : x 0 + 4 * x 1 + 9 * x 2 + 16 * x 3 + 25 * x 4 + 36 * x 5 + 49 * x 6 = 1)
    (h₁ : 4 * x 0 + 9 * x 1 + 16 * x 2 + 25 * x 3 + 36 * x 4 + 49 * x 5 + 64 * x 6 = 12)
    (h₂ : 9 * x 0 + 16 * x 1 + 25 * x 2 + 36 * x 3 + 49 * x 4 + 64 * x 5 + 81 * x 6 = 123) :
    16 * x 0 + 25 * x 1 + 36 * x 2 + 49 * x 3 + 64 * x 4 + 81 * x 5 + 100 * x 6 = 334 := by
  linarith