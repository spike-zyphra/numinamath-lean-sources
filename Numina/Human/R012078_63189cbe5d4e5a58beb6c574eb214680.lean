import Mathlib

/- From the given numbers $a, b, c, n$, we form the


$$

\begin{aligned}
p & =n a+(n+1) b+(n+1) c \\
q & =(n+3) a+(n+2) b+(n+3) c \\
r & =(n+3) a+(n+3) b+(n+2) c
\end{aligned}

$$


triple, then the


$$

p^{\prime}=2 s-p, \quad q^{\prime}=2 s-q, \quad r^{\prime}=2 s-r

$$


triple, where $s$ is the arithmetic mean of the numbers $p, q, r$. Show that the


$$

p^{k}+q^{k}+r^{k}=p^{\prime k}+q^{\prime k}+r^{\prime k}

$$


equality holds if $k=1,2$. -/
theorem algebra_173257 {a b c n p q r s : ℝ} (h₀ : p = n * a + (n + 1) * b + (n + 1) * c)
    (h₁ : q = (n + 3) * a + (n + 2) * b + (n + 3) * c) (h₂ : r = (n + 3) * a + (n + 3) * b + (n + 2) * c)
    (h₃ : s = (p + q + r) / 3) (h₄ : p' = 2 * s - p) (h₅ : q' = 2 * s - q)
    (h₆ : r' = 2 * s - r) :
    ∀ k ∈ Finset.Icc 1 2, p ^ k + q ^ k + r ^ k = p' ^ k + q' ^ k + r' ^ k := by
    intro k kh

    -- k is either 1 or 2
    have k_cases : k = 1 ∨ k = 2 := List.mem_pair.mp kh

    -- split on cases of k
    cases' k_cases with k1 k2
    -- k = 1 case
    · simp only [k1, pow_one]
      -- expand p' q' and r'
      have with_s : p' + q' + r' = 6 * s - (p + q + r) := by
        rw [h₄, h₅, h₆]
        ring

      -- simplify further, getting rid of s
      have cancel_s : 6 * s - (p + q + r) = (p + q + r) := by
        rw [h₃]
        ring

      -- chain equalities
      exact (with_s.trans cancel_s).symm
    -- k = 2 cases
    · rw [k2]

      -- expand p' q' and r'
      have expand_prime : p' ^ 2 + q' ^ 2 + r' ^ 2 = 3 * 4 * s ^ 2 - 4 * s * (p + q + r) + p ^ 2 + q ^ 2 + r ^ 2 := by
        rw [h₄, h₅, h₆]
        ring

      -- but the first two terms are zero
      have eq_zero : 3 * 4 * s ^ 2 - 4 * s * (p + q + r) = 0 := by
        rw [h₃]
        ring

      -- so the equality holds
      linarith only [expand_prime, eq_zero]