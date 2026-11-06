import Mathlib

open Nat Finset

/- Prove that for each positive integer $n$, there are pairwise relatively prime integers $k_{0}, \ldots, k_{n}$, all strictly greater than 1 , such that $k_{0} k_{1} \ldots k_{n}-1$ is the product of two consecutive integers. -/
theorem number_theory_604367 (n : ℕ) :
    ∃ k : Fin (n + 1) → ℕ,
      (∀ i j, i ≠ j → Nat.Coprime (k i) (k j)) ∧
      (∀ i, 1 < k i) ∧
      ∃ m, ∏ i : Fin (n + 1), k i = 1 + m * (m + 1) := by
  -- Proceed by induction on n
  induction n with
  | zero =>
    -- For $n = 0$, we can use $k_0 = 3$
    use 3
    simp only [reduceAdd, ne_eq, Pi.ofNat_apply, cast_ofNat, coprime_self, OfNat.ofNat_ne_one,
      imp_false, Decidable.not_not, one_lt_ofNat, implies_true, univ_unique, Fin.default_eq_zero,
      Fin.isValue, prod_const, card_singleton, pow_one, true_and]
    constructor
    · intros; ext; simp
    · use 1; norm_num
  | succ n ih =>
    -- Obtain $k_0,...,k_n$ and the $a$ for which $k_0 k_1 ... k_n = 1 + a (a + 1)$
    obtain ⟨k, ⟨k_coprime, one_lt_k, a, a_prod⟩⟩ := ih
    -- Use $k_{n+1} = a^2 + 3a + 3$
    use Fin.cons (a ^ 2 + 3 * a + 3) k
    -- For all $i ≤ n$, $k_i$ is coprime to $k_{n+1}$
    have coprime_new : ∀ i, Coprime (a ^ 2 + 3 * a + 3) (k i) := by
      -- because $\gcd(a^2+3a+3, a(a+1)+1) = \gcd(2(a+1), a(a+1)+1)$
      rw [← coprime_fintype_prod_right_iff, a_prod,
        show a ^ 2 + 3 * a + 3 = 1 + a * (a + 1) + 2 * (a + 1) by ring, coprime_self_add_left,
        add_comm 1]
      -- and $\gcd(a+1, a(a+1)+1) = \gcd(a+1, 1) = 1$
      rw [coprime_mul_iff_left, coprime_two_left, coprime_mul_right_add_right,
        coprime_one_right_eq_true, and_true]
      -- and $a(a+1)+1$ is odd
      exact Even.add_one (even_mul_succ_self a)
    refine ⟨fun i j hn ↦ ?_, fun i ↦ ?_, ?_⟩
    · -- For the pairwise relatively prime condition,
      -- split on whether or not the numbers in question are equal to $k_{n+1}$
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => contradiction
        | succ j => rw [Fin.cons_zero, Fin.cons_succ]; exact coprime_new j
      | succ i =>
        cases j using Fin.cases with
        | zero => rw [Fin.cons_zero, Fin.cons_succ]; exact (coprime_new i).symm
        | succ j =>
          rw [Fin.cons_succ]
          rw [ne_eq, Fin.succ_inj] at hn
          exact k_coprime i j hn
    · -- $1 < k_{n+1}$ is obvious
      cases i using Fin.cases <;> simp_all
    · -- The lower number in the "product of consecutive integers", given our choice of $k_{n+1}$,
      -- is $(a+1)^2$. The rest is pure algebraic manipulation (handled automatically by `ring`)
      use (a + 1) ^ 2
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, a_prod]
      ring
