import Mathlib

/- Let $f:(0,\infty) \rightarrow (0,\infty)$ be a function such that
\[ 
10\cdot \frac{x+y}{xy}=f(x)\cdot f(y)-f(xy)-90
\]
for every $x,y \in (0,\infty)$. What is $f(\frac 1{11})$?

$ 
\textbf{(A)}\ 1
\qquad\textbf{(B)}\ 11
\qquad\textbf{(C)}\ 21
\qquad\textbf{(D)}\ 31
\qquad\textbf{(E)}\ \text{There is more than one solution}
$ -/
theorem algebra_37396 {f : ℝ → ℝ} (hf : ∀ x > 0, f x > 0)
    (h : ∀ x y, 0 < x → 0 < y → 10 * (x + y) / (x * y) = f x * f y - f (x * y) - 90) :
    f (1 / 11) = 21 := by 
  -- Assume the given condition holds for various values
  have h₁ := h 1 1
  have h₂ := h 1 (1 / 11)
  have h₃ := h (1 / 11) 1
  have h₄ := h (1 / 11) (1 / 11)
  -- Simplify and use constraints and the structure of the equations
  norm_num at *
  -- Ensure non-zero function range
  nlinarith [hf 1 (by norm_num), hf (1 / 11) (by norm_num)]