import Mathlib

open Finset

/- Determine the general term $a_n$ of the sequence defined by the recurrence relation:
$a_{n+1}=\dfrac {2^{n+2}+1}{2^{n}-1} (a_n+1)-2^{n+3}-3$ for $n=1,2,3,\ldots$, with the initial condition $a_5=2014$. -/
theorem algebra_619242 {a : ℕ → ℝ}
(ha : ∀ n, a (n + 1) = (2^(n + 2) + 1) / (2^n - 1) * (a n + 1) - 2^(n + 3) - 3) (ha5 : a 5 = 2014) :
∀ n, a n = (41 - 2 * n) * (2^(n + 1) + 1) - 1 := by
  -- Introduce n as a variable
  intro n
  -- Apply the recurrence relation for n = 0
  have h0 := ha 0
  -- Simplify the expression using norm_num tactic
  norm_num at h0
  -- Apply the recurrence relation for n = 1
  have h1 := ha 1
  -- Simplify the expression
  norm_num at h1
  -- Apply the recurrence relation for n = 2
  have h2 := ha 2
  -- Simplify the expression
  norm_num at h2
  -- Apply the recurrence relation for n = 3
  have h3 := ha 3
  -- Simplify the expression
  norm_num at h3
  -- Apply the recurrence relation for n = 4
  have h4 := ha 4
  -- Simplify the expression
  norm_num at h4
  -- Apply the recurrence relation for n = 5
  have h5 := ha 5
  -- Simplify the expression
  norm_num at h5
  -- Use the initial condition a_5 = 2014
  have ha5' := ha5
  -- Use linear arithmetic to complete the proof
  linarith [ha5', h5]
