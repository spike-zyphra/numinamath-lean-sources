import Mathlib
/-- Elmer the emu takes $44$ equal strides to walk between consecutive telephone poles on a rural road. Oscar the ostrich can cover the same distance in $12$ equal leaps. The telephone poles are evenly spaced, and the $41$st pole along this road is exactly one mile ($5280$ feet) from the first pole. How much longer, in feet, is Oscar's leap than Elmer's stride?

$\textbf{(A) }6\qquad\textbf{(B) }8\qquad\textbf{(C) }10\qquad\textbf{(D) }11\qquad\textbf{(E) }15$ -/
theorem algebra_93189 (d s l : ℝ) (h₀ : d > 0) (h₁ : s > 0)
(h₂ : d = 44 * s) (h₃ : d = 12 * l) (h₄ : d * 40 = 5280) :
l - s = 8 := by
  -- There are $41-1=40$ gaps between the $41$ telephone poles, so the distance of each gap is $5280\div40=132$ feet.
  -- Each of Oscar's leaps covers $132\div12=11$ feet, and each of Elmer's strides covers $132\div44=3$ feet.
  -- Therefore, Oscar's leap is $11-3=\boxed{\textbf{(B) }8}$ feet longer than Elmer's stride.
  linarith