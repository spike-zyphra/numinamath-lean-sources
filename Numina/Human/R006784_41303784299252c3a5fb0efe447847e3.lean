import Mathlib

/-Let $g(k)=k$ for any integer $k$.
Consider the expression $$N_g(X_0) = \left\lfloor 10^{4} \cdot \frac{\sum_{n=2}^{X_0} g\left(n^{2}-1\right)}
{\sum_{n=2}^{X_0} g(n)}\right\rfloor.$$ Show that for $X_0=10$, the value of $N_g(10)$ is $69444$.-/

theorem number_theory_641121:
  ⌊10^4 * ((∑ n ∈ Finset.Icc (2: ℕ) 10, (n ^ 2 - 1)): ℝ) /  (∑ n ∈ Finset.Icc (2: ℕ) 10, n)⌋ = 69444 := by

  simp [Finset.sum_Icc_succ_top]
  norm_num