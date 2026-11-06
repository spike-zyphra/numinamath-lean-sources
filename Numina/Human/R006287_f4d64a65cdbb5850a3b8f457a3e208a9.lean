import Mathlib
/- Let $N$ be an integer. Show that if $N$ is a multiple of 6, then for any integer $k$, the five integers $Nk - 1, Nk + 1, Nk + 2, Nk + 3, Nk + 5$ are pairwise relatively prime. -/
theorem number_theory_635536 (n k : ℤ) (hn : 6 ∣ n) : IsCoprime (n * k - 1) (n * k + 1) ∧ IsCoprime (n * k - 1) (n * k + 2) ∧ IsCoprime (n * k - 1) (n * k + 3) ∧ IsCoprime (n * k - 1) (n * k + 5) ∧ IsCoprime (n * k + 1) (n * k + 2) ∧ IsCoprime (n * k + 1) (n * k + 3) ∧ IsCoprime (n * k + 1) (n * k + 5) ∧ IsCoprime (n * k + 2) (n * k + 3) ∧ IsCoprime (n * k + 2) (n * k + 5) ∧ IsCoprime (n * k + 3) (n * k + 5):= by

  -- Since n is divisible by 6, we can write n = 6m for some integer m
  rcases hn with ⟨m, hm⟩
  subst n

  -- We need to prove 10 pairs are coprime, so we'll use refine to break it into 10 subgoals
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  -- Prove nk-1 and nk+1 are coprime
  .
    use 3 * m * k, (1 - 3 * m * k)
    ring

  -- Prove nk-1 and nk+2 are coprime
  .
    use -(1 + 2 * m * k), 2 * m * k
    ring

  -- Prove nk-1 and nk+3 are coprime using the fact that their difference is 4 = 2²
  .
    suffices IsCoprime (6 * m * k - 1) (6 * m * k + 3 + -1 * (6 * m * k - 1)) by exact IsCoprime.add_mul_right_right_iff.mp this
    ring_nf
    rw [show (4 : ℤ) = 2 ^ 2 by ring]
    suffices IsCoprime (-1 + m * k * 6) 2 by exact IsCoprime.symm (IsCoprime.pow_left (id (IsCoprime.symm this)))
    use -1, 3 * m * k
    ring

  -- Prove nk-1 and nk+5 are coprime
  .
    suffices IsCoprime (6 * m * k - 1) (6 * m * k + 5 + -1 * (6 * m * k - 1)) by exact IsCoprime.add_mul_right_right_iff.mp this
    ring_nf
    use -1, m * k
    ring_nf

  -- Prove nk+1 and nk+2 are coprime
  .
    use -1, 1
    ring_nf

  -- Prove nk+1 and nk+3 are coprime
  .
    suffices IsCoprime (6 * m * k + 1) (6 * m * k + 3 + -1 * (6 * m * k + 1)) by exact IsCoprime.add_mul_right_right_iff.mp this
    ring_nf
    use 1, -3 * m * k
    ring_nf

  -- Prove nk+1 and nk+5 are coprime using the fact that their difference is 4 = 2²
  .
    suffices IsCoprime (6 * m * k + 1) (6 * m * k + 5 + -1 * (6 * m * k + 1)) by exact IsCoprime.add_mul_right_right_iff.mp this
    ring_nf
    rw [show (4 : ℤ) = 2 ^ 2 by ring]
    suffices IsCoprime (1 + m * k * 6) 2 by exact IsCoprime.symm (IsCoprime.pow_left (id (IsCoprime.symm this)))
    use 1, -3 * m * k
    ring_nf

  -- Prove nk+2 and nk+3 are coprime
  .
    use -1, 1
    ring_nf

  -- Prove nk+2 and nk+5 are coprime using properties of coprimality with 3
  .
    suffices IsCoprime (6 * m * k + 2) (6 * m * k + 5 + -1 * (6 * m * k + 2)) by exact IsCoprime.add_mul_right_right_iff.mp this
    ring_nf
    suffices IsCoprime 3 (2 + m * k * 6) by exact id (IsCoprime.symm this)
    suffices IsCoprime 3 (2 + m * k * 6 + -(2 * m * k) * 3) by exact IsCoprime.add_mul_right_right_iff.mp this
    ring_nf
    use 1, -1
    ring_nf

  -- Prove nk+3 and nk+5 are coprime
  .
    suffices IsCoprime (6 * m * k + 3) (6 * m * k + 5 + -1 * (6 * m * k + 3)) by exact IsCoprime.add_mul_right_right_iff.mp this
    ring_nf
    use 1 , -(3 * m * k + 1)
    ring_nf
