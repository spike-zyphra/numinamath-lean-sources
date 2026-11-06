import Mathlib

open Finset

/- 18. A sequence of polynomials $a_{n}(x)$ are defined recursively by
$$
\begin{array}{l}
a_{0}(x)=1, \\
a_{1}(x)=x^{2}+x+1, \\
a_{n}(x)=\left(x^{n}+1\right) a_{n-1}(x)-a_{n-2}(x), \text { for all } n \geq 2 .
\end{array}
$$

For example,
$$
\begin{aligned}
a_{2}(x) & =\left(x^{2}+1\right)\left(x^{2}+x+1\right)-1=x^{4}+x^{3}+2 x^{2}+x, \\
a_{3}(x) & =\left(x^{3}+1\right)\left(x^{4}+x^{3}+2 x^{2}+x\right)-\left(x^{2}+x+1\right) \\
& =x^{7}+x^{6}+2 x^{5}+2 x^{4}+x^{3}+x^{2}-1 .
\end{aligned}
$$

Evaluate $a_{2010}(1)$. -/
theorem algebra_288559 {a : ℕ → ℝ → ℝ}
    -- Initial condition: a_0(x) = 1 for all x
    (ha0 : ∀ x, a 0 x = 1)
    -- Initial condition: a_1(x) = x^2 + x + 1 for all x
    (ha1 : ∀ x, a 1 x = x ^ 2 + x + 1)
    -- Recursive definition: a_n(x) = (x^n + 1) * a_{n-1}(x) - a_{n-2}(x) for n ≥ 2
    (han : ∀ n ≥ 2, ∀ x, a n x = (x ^ n + 1) * a (n - 1) x - a (n - 2) x) :
    a 2010 1 = 4021 := by
  -- We prove that a_n(1) = 2n + 1 for all natural numbers n
  have h1 : ∀ n, a n 1 = 2 * n + 1 := by
    intro n
    -- We use two-step induction since the recurrence relation involves terms n, n-1, and n-2
    induction n using Nat.twoStepInduction with
    -- Base case: n = 0
    | zero =>
      rw [ha0]
      norm_num
    -- Base case: n = 1
    | one =>
      rw [ha1]
      norm_num
    -- Inductive step: assuming the formula holds for n and n+1, prove it for n+2
    | more n ih1 ih2 =>
      have h := han (n + 2) (by linarith) 1
      simp [ih1, ih2] at h ⊢
      linarith
  -- Apply our formula to n = 2010
  have h := h1 2010
  norm_num at h
  linarith
