import Mathlib

/- 14.36. Let $n=p_{1}^{a_{1}} \ldots p_{k}^{a_{k}}$ be the prime factorization of the number, $\varphi(n)$ the number of integers from 1 to $n$,
coprime with $n$. Prove that


$$

\varphi(n)=n\left(1-\frac{1}{p_{1}}\right)\left(1-\frac{1}{p_{2}}\right) \ldots\left(1-\frac{1}{p_{k}}\right)

$$
 -/
theorem number_theory_226323 {n : ℕ} (hn : n ≠ 0) :
    n.totient = n * ∏ p ∈ n.primeFactors, (1 - 1 / p : ℚ) := by
  -- Use the Euler product formula for the totient function
  rw [Nat.totient_eq_mul_prod_factors]
  simp