import Mathlib

/-
Problem

When $x=m$ and $x=n$ (where $m \neq n$), the values of the quadratic function $y=x^2-2x+3$ are equal. What is the value of this function when $x=m+n$?
-/

/-
Solution
Given that the function values are identical for $x=m$ and $x=n$, and observing that the function can be expressed as
$$y=(x-1)^2+2,$$
we can deduce that the points with coordinates $(m, y)$ and $(n, y)$ are symmetric about the line $x=1$. This symmetry implies that the midpoint of the line segment connecting the two points lies on the line $x=1$. Therefore, we can establish the equation
$$\frac{m+n}{2}=1.$$

By solving this equation, we get
$$m+n=2.$$

Since we are interested in the function value when $x=m+n$, we can substitute $2$ for $x$ into the function, yielding
$$y=(2)^2-2\cdot2+3.$$

Simplifying the expression, we obtain
$$y=4-4+3.$$

Therefore, the function value when $x=m+n$ is
$$\boxed{y=3}.$$

This problem explores the characteristic coordinates of points on the graph of a quadratic function, particularly exploiting the function's symmetry and the formula for the axis of symmetry, which is essential for solving the problem. Remembering these properties and deducing that $m+n=2$ is key to the solution.
-/

-- Define the quadratic function f(x) = x^2 - 2x + 3
def f_9438 (x : ℝ) : ℝ := x^2 - 2 * x + 3

-- Prove that if f(m) = f(n) and m ≠ n, then f(m + n) = 3
theorem algebra_9438 : ∀ m n : ℝ, (m ≠ n) ∧ (f_9438 m = f_9438 n) → f_9438 (m + n) = 3 := by

  intro m n h
  rcases h with ⟨hmn, hfn⟩

  -- Substitute the function definition into the equation hfn
  have eq1 : m ^ 2 - 2 * m + 3 = n ^ 2 - 2 * n + 3 := by
    simpa [f_9438] using hfn

  -- Simplify the equation to m^2 - 2m = n^2 - 2n
  have eq2 : m ^ 2 - 2 * m = n ^ 2 - 2 * n := by
    linarith

  -- Rearrange terms to factor the equation
  have eq3 : (m - n) * (m + n - 2) = 0 := by
    nlinarith

  -- Since m ≠ n, we know m - n ≠ 0
  have eq4 : m + n - 2 = 0 := by
    apply (mul_left_inj' (show (m - n : ℝ) ≠ 0 by
        intro h'
        apply hmn
        linarith
    )).mp
    linarith

  -- Therefore, m + n = 2
  have eq5 : m + n = 2 := by
    linarith

  -- Calculate f(m + n)
  have eq6 : f_9438 (m + n) = 3 := by
    rw [f_9438]
    rw [show m + n = 2 by linarith [eq5]]
    norm_num

  -- Prove the final result
  exact eq6