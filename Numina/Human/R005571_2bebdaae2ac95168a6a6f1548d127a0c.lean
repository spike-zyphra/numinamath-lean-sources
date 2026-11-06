import Mathlib

/- For positive integers $m, n$, let $\operatorname{gcd}(m, n)$ denote the largest positive integer that is a factor of both $m$ and $n$. Compute

$$
\sum_{n=1}^{91} \operatorname{gcd}(n, 91) .
$$-/
theorem number_theory_608913 :
    ∑ n ∈ Finset.Icc 1 (91 : ℕ), Nat.gcd n 91 = 325 := by
  norm_num [Finset.sum_Icc_succ_top]