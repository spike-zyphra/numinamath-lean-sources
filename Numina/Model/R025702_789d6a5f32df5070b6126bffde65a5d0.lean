import Mathlib

theorem algebra_602039 (a b c d : ℤ) (h : ∀ m n, ∃ x y : ℤ, a * x + b * y = m ∧ c * x + d * y = n) :
    a * d - b * c = 1 ∨ a * d - b * c = -1 := by

  have h1 := h 1 0
  rcases h1 with ⟨x1, y1, h1x, h1y⟩
  -- Apply the hypothesis to solve for (0, 1).
  have h2 := h 0 1
  rcases h2 with ⟨x2, y2, h2x, h2y⟩
  -- Let $N = \begin{pmatrix} x1 & y1 \\ x2 & y2 \end{pmatrix}$ and $A^T = \begin{pmatrix} a & c \\ b & d \end{pmatrix}$.
  -- From the conditions we have $N \cdot A^T = I$.
  -- The determinant of $A^T$ is $a * d - b * c$.
  -- The determinant of $N$ is $x1 * y2 - x2 * y1$.
  -- We have $\det(N) \cdot \det(A^T) = 1$, so $\det(N) \cdot (a * d - b * c) = 1$.
  have h5 : (a * d - b * c) * (x1 * y2 - x2 * y1) = 1 := by
    nlinarith [sq_nonneg (a * y1 - b * x1), sq_nonneg (c * y1 - d * x1), sq_nonneg (a * y2 - b * x2), sq_nonneg (c * y2 - d * x2), sq_nonneg (x1 * d - y1 * c), sq_nonneg (x2 * b - y2 * a)]
  -- If the product of two integers is 1, then they must be either 1 or -1.
  have h6 : (a * d - b * c) * (x1 * y2 - x2 * y1) = 1 := h5
  -- Use the theorem that if $x \cdot y = 1$ then $x = 1$ or $x = -1$.
  have h7 : a * d - b * c = 1 ∨ a * d - b * c = -1 := by
    apply Int.eq_one_or_neg_one_of_mul_eq_one 
    exact h6
  -- The result is exactly what we need.
  exact h7