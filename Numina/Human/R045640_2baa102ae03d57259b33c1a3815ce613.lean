import Mathlib
/- Let $a, b$, and $c$ be real numbers. Consider the system of simultaneous equations in variables $x$ and $y$ :

$$
\begin{aligned}
a x+b y & =c-1 \\
(a+5) x+(b+3) y & =c+1
\end{aligned}
$$

Determine the value(s) of $c$ in terms of $a$ such that the system always has a solution for any $a$ and $b$. -/
theorem algebra_608520 (a c : ℝ) : (∀ b : ℝ, ∃ x y : ℝ, a * x + b * y = c - 1 ∧ (a + 5) * x + (b + 3) * y = c + 1) ↔ c = 2 * a / 5 + 1:= by
  constructor
  -- Forward direction: prove that if system has solution for all b, then c = 2a/5 + 1
  .
    intro h
    -- Choose b = 3a/5 as a special case
    specialize h (3 / 5 * a)
    rcases h with ⟨x, y, h1, h2⟩
    -- Simplify the second equation
    replace h2 : 5 * x + 3 * y = 2:= by linarith
    -- Rewrite first equation in terms of the simplified form
    replace h1 : a / 5 * (5 * x + 3 * y) = c - 1:= by linarith
    rw [h2] at h1
    linarith
  -- Reverse direction: prove that if c = 2a/5 + 1, then system has solution for all b
  .
    intro h
    subst c
    intro b
    -- Use x = 2/5 and y = 0 as the solution
    use (2 / 5), 0
    constructor
    all_goals
      linarith
