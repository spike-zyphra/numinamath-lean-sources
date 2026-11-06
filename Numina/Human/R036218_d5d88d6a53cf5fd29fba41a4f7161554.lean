import Mathlib
/- Let $f(x, y)=x^{2}+2 x+y^{2}+4 y$. Let $\left(x_{1}, y_{1}\right),\left(x_{2}, y_{2}\right),\left(x_{3}, y_{3}\right)$, and $\left(x_{4}, y_{4}\right)$ be the vertices of a square with side length one and sides parallel to the coordinate axes. What is the minimum value of $f\left(x_{1}, y_{1}\right)+f\left(x_{2}, y_{2}\right)+f\left(x_{3}, y_{3}\right)+f\left(x_{4}, y_{4}\right) ?$ -/
theorem algebra_608747 (f : ℝ → ℝ → ℝ) (hf : f = fun x y => x ^ 2 + 2 * x + y ^ 2 + 4 * y) : IsLeast {S : ℝ | ∃ x y : ℝ, S = f x y + f (x + 1) y + f x (y + 1) + f (x + 1) (y + 1)} (-18):= by
  constructor
  -- First part: Prove that -18 is achievable
  .
    simp
    -- Use the point (-3/2, -5/2) as the lower-left vertex of the square
    use (-3 / 2), (-5 / 2)
    simp [hf]
    norm_num
  -- Second part: Prove that -18 is the minimum possible value
  .
    simp [lowerBounds]
    intro S x y hS
    subst S
    simp [hf]
    -- Use the fact that sum of squares is non-negative
    have h1 : (x + 3 / 2) ^ 2 + (y + 5 / 2) ^ 2 ≥ 0:= by positivity
    linarith
