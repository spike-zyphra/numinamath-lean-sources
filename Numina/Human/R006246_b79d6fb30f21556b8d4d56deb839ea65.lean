import Mathlib
/- Let $a$ be a natural number and $N$ be a positive natural number.
Theorem: The tens digit of the sum $S = \sum_{k=1}^N (10a+1)^k$ is $\lfloor V/10 \rfloor$, where $V = (N + 5aN(N+1)) \pmod{100}$ and the result of the $\pmod{100}$ operation is taken in the set $\{0, 1, \ldots, 99\}$. -/
theorem number_theory_635118 (a n : ℕ) : (∑ i in Finset.range n, (10 * a + 1) ^ (i + 1)) % 100 / 10 = (n + 5 * a * n * (n + 1)) % 100 / 10:= by

  -- First lemma: Proves that (10a + 1)^n is congruent to 10an + 1 modulo 100 for all natural numbers n
  have h1 : ∀ n : ℕ, (10 * a + 1) ^ n ≡ 10 * a * n + 1 [MOD 100]:= by
    intro n
    -- Proof by induction on n
    induction n with
    -- Base case: n = 0
    | zero =>
      simp
      rfl
    -- Inductive step: Prove for n + 1 assuming it holds for n
    | succ n ih =>
      -- Rewrite (10a + 1)^(n+1) as (10a + 1)^n * (10a + 1)
      rw [show (10 * a + 1) ^ (n + 1) = (10 * a + 1) ^ n * (10 * a + 1) by ring]
      -- Apply inductive hypothesis with multiplication property of congruences
      replace ih : (10 * a + 1) ^ n * (10 * a + 1) ≡ (10 * a * n + 1) * (10 * a + 1) [MOD 100]:= by exact Nat.ModEq.mul ih rfl
      -- Expand the right side algebraically
      rw [show (10 * a * n + 1) * (10 * a + 1) = 100 * (a ^ 2 * n) + 10 * a + 10 * a * n + 1 by ring] at ih
      -- Prove that terms with factor 100 vanish modulo 100
      have g1 : 100 * (a ^ 2 * n) + 10 * a + 10 * a * n + 1 ≡ 10 * a + 10 * a * n + 1 [MOD 100]:= by
        have g1 : 100 * (a ^ 2 * n) ≡ 0 [MOD 100]:= by
          suffices 100 ∣ 100 * (a ^ 2 * n) by exact Nat.modEq_zero_iff_dvd.mpr this
          simp
        replace g1 : 100 * (a ^ 2 * n) + (10 * a + 10 * a * n + 1) ≡ 0 + (10 * a + 10 * a * n + 1) [MOD 100]:= by exact Nat.ModEq.add_right (10 * a + 10 * a * n + 1) g1
        simp at g1
        rw [show 100 * (a ^ 2 * n) + 10 * a + 10 * a * n + 1 = 100 * (a ^ 2 * n) + (10 * a + 10 * a * n + 1) by ring]
        exact g1
      -- Simplify to complete the inductive step
      rw [show 10 * a + 10 * a * n + 1 = 10 * a * (n + 1) + 1 by ring] at g1
      exact Nat.ModEq.trans ih g1

  -- Second lemma: Proves that the sum of powers is congruent to n + 5an(n+1) modulo 100
  have h2 : ∀ n : ℕ, ∑ i in Finset.range n, (10 * a + 1) ^ (i + 1) ≡ n + 5 * a * n * (n + 1) [MOD 100]:= by
    intro n
    -- Proof by induction on n
    induction n with
    -- Base case: n = 0
    | zero =>
      simp
      rfl
    -- Inductive step: Prove for n + 1 assuming it holds for n
    | succ n ih =>
      rw [Finset.sum_range_succ]
      specialize h1 (n + 1)
      replace ih:= Nat.ModEq.add ih h1
      rw [show n + 5 * a * n * (n + 1) + (10 * a * (n + 1) + 1) = n + 1 + 5 * a * (n + 1) * (n + 1 + 1) by ring] at ih
      exact ih

  -- Apply the second lemma to complete the proof
  rw [h2 n]
