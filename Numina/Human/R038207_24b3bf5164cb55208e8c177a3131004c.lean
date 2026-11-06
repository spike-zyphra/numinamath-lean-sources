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
  classical -- Use classical logic to handle non-constructive cases
  intro m n ⟨neq, eq⟩ -- Introduce variables m, n and the hypothesis ⟨m ≠ n, f(m) = f(n)⟩

  unfold f_9438 at eq -- Expand the definition of f in the hypothesis f(m) = f(n)

  -- Simplify the equation by canceling identical terms on both sides
  simp only [add_left_inj] at eq

  -- Prove that m^2 - n^2 = 2 * m - 2 * n by manipulating both sides
  have : m^2 - n^2 = 2 * m - 2 * n := by
    apply_fun (· + 2 * m) at eq -- Add 2 * m to both sides of the equation
    simp only [sub_add_cancel] at eq -- Simplify by canceling terms
    apply_fun (· - n ^ 2) at eq -- Subtract n^2 from both sides
    have : n^2 - 2 * n + 2 * m - n^2 = 2 * m - 2 * n := by
      ring -- Simplify using basic algebra
    rw [this] at eq -- Substitute into eq
    exact eq

  -- Rewrite m^2 - n^2 as (m - n)(m + n)
  rw [sq_sub_sq m n] at this

  -- Rewrite 2 * m - 2 * n as 2 * (m - n)
  have mn : 2 * m - 2 * n = 2 * (m - n) := by ring
  rw [mn] at this

  -- Show that m + n = 2
  have foo : m + n = 2 := by
    -- Since m ≠ n, m - n ≠ 0
    have mnneq0 : m - n ≠ 0 := by
      exact sub_ne_zero_of_ne neq
    -- Divide both sides of the equation by (m - n) to isolate m + n
    apply_fun (· * (1 / (m - n))) at this
    simp only [one_div, mul_eq_mul_right_iff, inv_eq_zero, or_self_right] at this
    -- Handle cases and conclude m + n = 2
    rcases this with (h1 | h2)
    · exact h1 -- If the first case holds, we get m + n = 2
    · exact False.elim (mnneq0 h2) -- Contradiction if m - n = 0

  -- Substitute m + n = 2 into f and simplify
  unfold f_9438
  rw [foo]

  -- Simplify f(2) = 3
  simp only [add_left_eq_self]
  have : 2 * 2 = (2 ^ 2 : ℝ) := by
    exact Eq.symm (pow_two 2)
  rw [this]
  simp only [sub_self]
