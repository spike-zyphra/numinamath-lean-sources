import Mathlib

/- Given a sequence $\{a_n\}$ where $a_n = n^2 + \lambda n$, and $a_n$ is an increasing sequence, find the range of the real number $\lambda$.-/
theorem algebra_9037 (ω : ℝ) (a : ℕ → ℝ) (ha : ∀ n > 0, a n = n ^ 2 + ω * n)
    (hinc : ∀ n > 0, a n < a (n + 1)) :
    ω > -3 := by
  -- Since $a_n = n^2 + \lambda n$, we have $a_{n+1} = (n+1)^2 + \lambda (n+1)$.
  have h1 := ha 1 (by norm_num)
  have h2 := ha 2 (by norm_num)
  -- Because $a_n$ is an increasing sequence, it follows that $(n+1)^2 + \lambda (n+1) - n^2 - \lambda n > 0$.
  have h := hinc 1 (by norm_num)
  rw [h1, h2] at h
  -- Simplifying, we get $2n + 1 + \lambda > 0$.
  norm_num at h
  -- Therefore, $\lambda > -2n - 1$.
  -- Since this must hold for any positive integer, we have $\lambda > -3$.
  -- Thus, the answer is $\boxed{(-3, +\infty)}$.
  linarith
