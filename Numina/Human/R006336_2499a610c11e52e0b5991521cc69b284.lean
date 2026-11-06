import Mathlib

/-E94

Let $K$ be an integer such that $K \ge 2$. Let $S_K$ denote the sum of all positive integers $m$ such that
$\frac{K!}{m}$ is a perfect square. Let $P_1^{a_1} P_2^{a_2} \cdots P_r^{a_r}$ be the prime factorization of $S_K$,
where $P_i$ are distinct prime numbers and $a_i$ are positive integers.

We define $V_K = a_1 + a_2 + \cdots + a_r$.

Compute $V_K$ for $K=5$. Show the answer is 4.-/

theorem number_theory_636052 (S V: ℕ) (h1: S = ∑ᶠ i ∈ {m: ℕ | m ∣ Nat.factorial 5 ∧ IsSquare (Nat.factorial 5 / m)}, i)
  (h2: V = ∑ p ∈ Nat.primeFactors S, S.factorization p): V = 4 := by

  -- we compute S first
  replace h1: S = 150 := by
    clear h2
    rw [h1]
    clear h1
    have h_eq: {m | m ∣ Nat.factorial 5 ∧ IsSquare (Nat.factorial 5 / m)} = {120, 30} := by
      rw [show Nat.factorial 5 = 120 by native_decide]
      ext m
      constructor

      -- the forward direction
      .
        intro h
        simp
        simp at h
        rcases h with ⟨h1, h2⟩
        replace h1: m ∈ Nat.divisors 120 := by
          simp
          tauto
        rw [show Nat.divisors 120 = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} by native_decide] at h1
        simp at h1
        by_contra! no
        rcases h1 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        all_goals simp [h] at h2 no
        all_goals absurd h2; native_decide

      -- the backward direction
      .
        intro h
        simp at h
        rcases h with h | h
        .
          simp [h]
        .
          simp [h]
          native_decide

    rw [h_eq]
    rw [finsum_mem_eq_toFinset_sum]
    simp

  -- then we can compute V
  rw [h1] at h2
  rw [h2]
  clear h1 h2
  native_decide