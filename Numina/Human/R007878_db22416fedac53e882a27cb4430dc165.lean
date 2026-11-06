import Mathlib

/- If $f(x)$ is a function, then we define the function $f^{(n)}(x)$ to be the result of $n$ applications of $f$ to $x$, where $n$ is a positive integer. For example, $f^{(3)}(x)=f(f(f(x)))$.

We define the $\textit{order}$ of an input $x$ with respect to $f$ to be the smallest positive integer $m$ such that $f^{(m)}(x)=x$.

Now suppose $f(x)$ is the function defined as the remainder when $x^2$ is divided by $11$. What is the order of $5$ with respect to this function $f$? -/
theorem number_theory_16401 (f : ℕ → ℕ) (x : ℕ) (hf : f = fun y => y ^ 2 % 11) (hx : x = 5) :
    IsLeast {m | 0 < m ∧ f^[m] x = x} 4 := by
  rw [hf, hx]
  clear * -
  -- The least number of iterations is 4
  constructor
  . -- f^[4] 5 = 5
    simp
  . -- We prove that 4 is the least number in the set
    intro m hm
    by_contra! hm'
    -- By proving that 0, 1, 2, 3 are not in the set
    interval_cases m <;> simp at hm
