import Mathlib

-- Let $k_0$ be an odd positive integer such that $k_0 \ge 3$. Let $S = 2^{k_0}+4$. It is given that $2^{k_0-2}+1 = p_1^{e_1} p_2^{e_2} \dots p_j^{e_j}$ is the prime factorization of $2^{k_0-2}+1$, where $p_i$ are distinct odd primes and $e_i$ are positive integers. Show that the product of all positive divisors of $S$ is equal to $S^E$, where $E = \frac{3}{2}(e_1+1)(e_2+1)\dots(e_j+1)$.

theorem number_theory_637486 {k0 S N: ℕ}
  (hk0 : 3 ≤ k0)
  (hS : S = 2^k0 + 4) (hN : N = 2^(k0 - 2) + 1) :
  (∏ p ∈ S.divisors, p)^2 = S^(3 * ∏ p ∈ N.primeFactors, (S.factorization p + 1)) := by

  have hS_ne_zero : S ≠ 0 := by
    by_contra h
    subst S
    simp at h

  have hSN : S = 4 * N := by
    rw [hS, hN]
    let x := k0 - 2
    have hx : 1 ≤ x := by omega
    have hxk : k0 = x + 2 := by omega
    rw [hxk]
    ring_nf
    simp

  have hN_ne_zero : N ≠ 0 := by omega

  have hN_odd : Odd N := by
    use 2^(k0 - 3)
    nth_rw 1 [show 2=2^1 by norm_num]
    rw [← Nat.pow_add]
    rw [show 1 + (k0 - 3) = k0 - 2 by omega]
    rw [hN]

  rw [pow_two]
  nth_rw 1 [← Nat.prod_div_divisors]
  rw [← Finset.prod_mul_distrib]

  rw [Finset.prod_congr rfl (fun x hx => by
    rw [Nat.div_mul_cancel]
    simp at hx
    exact hx.1
  )]

  simp
  suffices S.divisors.card = (3 * ∏ p ∈ N.primeFactors, (S.factorization p + 1)) by
    rw [this]

  rw [Nat.card_divisors hS_ne_zero]
  let f := fun p => S.factorization p + 1
  rw [show 3 = f 2 by
    unfold f
    rw [hSN]
    rw [Nat.factorization_mul (by norm_num) hN_ne_zero]
    simp
    rw [show N.factorization 2 = 0 by
      apply Nat.factorization_eq_zero_of_not_dvd
      contrapose hN_odd
      simp
      rw [even_iff_two_dvd]
      omega
    ]
    norm_num
    native_decide
  ]
  rw [show N.primeFactors = S.primeFactors.erase 2 by
    ext p
    simp
    constructor
    . intro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      . contrapose hN_odd
        simp at hN_odd
        rw [hN_odd] at h2
        simp
        rw [even_iff_two_dvd]
        exact h2
      . exact h1
      . obtain ⟨k, hk⟩ := h2
        use 4*k
        linarith
      . exact hS_ne_zero
    . intro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_⟩
      . exact h2
      . rw [hSN] at h3
        rw [Nat.Prime.dvd_mul] at h3
        . rcases h3 with h | h
          . have : p ≤ 4 := by
              apply Nat.le_of_dvd (by norm_num) at h
              exact h
            interval_cases p
            all_goals try omega
            contrapose h2
            decide
          . exact h
        . exact h2
      . exact hN_ne_zero
  ]
  symm

  apply Finset.mul_prod_erase
  simp
  refine ⟨?_, ?_, ?_⟩
  . decide
  . use 2 * N
    omega
  . exact hS_ne_zero
