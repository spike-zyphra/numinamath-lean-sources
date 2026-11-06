import Mathlib
open Mathlib
/-- In order to estimate the value of $x-y$ where $x$ and $y$ are real numbers with $x>y>0$, Xiaoli rounded $x$ up by a small amount, rounded $y$ down by the same amount, and then subtracted her rounded values. Which of the following statements is necessarily correct?

$\textbf{(A) } \text{Her estimate is larger than } x - y \qquad \textbf{(B) } \text{Her estimate is smaller than } x - y \qquad \textbf{(C) } \text{Her estimate equals } x - y$ $\textbf{(D) } \text{Her estimate equals } y - x \qquad \textbf{(E) } \text{Her estimate is } 0$ -/
theorem algebra_95437 (x y k : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x > y) (hk : 0 < k) :
(x + k) - (y - k) > x - y := by
  -- The original expression $x-y$ now becomes $(x+k) - (y-k)=(x-y)+2k>x-y$, where $k$ is a positive constant, hence the answer is $\boxed{\textbf{(A)}}$.
  have step1: (x + k) - (y - k) = x - y + 2 * k := by ring
  rw [step1]
  linarith