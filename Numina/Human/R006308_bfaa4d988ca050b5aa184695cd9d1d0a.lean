import Mathlib

/- Let $X$ be an integer that is not divisible by 3. Let $K = 3X+1$. Let $S$ be an arbitrary integer.
Suppose $M$ and $N$ are natural numbers, $M < 10$ and $N < 10$.
If the equation $(100M + 10N + 1) - (10M + N) = K$ holds, show that $M + N = S$. -/
theorem number_theory_635720 (X : ℕ) (hX : ¬ 3 ∣ X) (K : ℕ) (hK : K = 3 * X + 1)
    (M N : ℕ) (hmn : M < 10 ∧ N < 10) (H : ((100 * M + 10 * N + 1) - (10 * M + N) : ℤ) = K)
    (S : ℤ) :
    S = M + N :=
by
  exfalso
  have : 90 * M + 9 * N + 1 = K := by
    zify
    linarith
  subst hK
  have : 90 * M + 9 * N = 3 * X := by
    omega
  have : 30 * M + 3 * N = X := by
    omega
  subst this
  omega
