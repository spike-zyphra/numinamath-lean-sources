import Mathlib

/- The function $f$ satisfies \[
f(x) + f(2x+y) + 5xy = f(3x - y) + 2x^2 + 1
\]for all real numbers $x,y$. Determine the value of $f(10)$. -/
theorem algebra_16237 {f : ℝ → ℝ} (h : ∀ x y, f x + f (2 * x + y) + 5 * x * y = f (3 * x - y) + 2 * x ^ 2 + 1) :
    f 10 = -49 := by
  have h1 := h 10 0
  have h2 := h 0 10
  have h3 := h 10 10
  ring_nf at h1 h2 h3
  linarith