import Mathlib

/- # Problem:
 Find all pairs $(m, n) \in \mathbb{Z}^+ \times \mathbb{Z}^+$ such that $n \mid 2^{m-1} + 1$ and $m \mid 2^{n-1} + 1$.
 1. **Lemma:** If $p \mid a^{2^n} + 1$ for $a > 1$, then $p \equiv 1 \pmod{2^{n+1}}$.
 2. **Proof of Lemma:**
 3. Let $d = \operatorname{ord}\_p(a)$, which is the smallest positive integer such that $a^d \equiv 1 \pmod{p}$.
 4. We have $a^{2^{n+1}} \equiv 1 \pmod{p}$ and $a^{p-1} \equiv 1 \pmod{p}$ by Fermat's Little Theorem.
 5. Therefore, $d \mid 2^{n+1}$ and $d \mid (p-1)$.
 6. Assume $d < 2^{n+1}$. Then $d \mid 2^n$, which implies $a^{2^n} \equiv 1 \pmod{p}$.
 7. Since $p \mid a^{2^n} + 1$, we have $p \mid (a^{2^n} - 1) + 2 = a^{2^n} + 1$.
 8. This leads to $p \mid 2$, which is a contradiction because $p$ is an odd prime.
 9. Therefore, $d = 2^{n+1}$, and hence $p \equiv 1 \pmod{2^{n+1}}$.
10. **Back to the Problem:**
11. If $m, n \leq 2$, then the pairs $(m, n)$ are $(1, 1)$, $(1, 2)$, and $(2, 1)$.
12. If $m, n > 2$:
13. Let $m-1 = 2^a \times u$ and $n-1 = 2^b \times v$ where $u$ and $v$ are odd.
14. Let $p \mid n$. Then $p \mid (2^{m-1} + 1) = (2^u)^{2^a} + 1$.
15. By the lemma, $p \equiv 1 \pmod{2^{a+1}}$.
16. Let $m = 2^{a+1} \times k + 1$. Then $2^b v = n-1 = 2^{a+1} k$.
17. Since $v$ is odd, $2^b \mid 2^{a+1} k$, which implies $b \geq a+1$.
18. Similarly, if $q \mid m$, then $q \mid (2^{n-1} + 1) = (2^v)^{2^b} + 1$.
19. By the lemma, $q \equiv 1 \pmod{2^{b+1}}$.
20. Let $m = 2^{b+1} \times l + 1$. Then $2^a u = m-1 = 2^{b+1} l$.
21. Since $u$ is odd, $2^a \mid 2^{b+1} l$, which implies $a \geq b+1$.
22. This leads to a contradiction because $b \geq a+1$ and $a \geq b+1$ cannot both be true.
23. Therefore, the only pairs $(m, n)$ satisfying the problem are \\boxed{(1, 1), (1, 2), (2, 1)}. -/


lemma number_theory_612625_lemma_1 (p a n : ℕ) (hprime : Nat.Prime p) (hodd : Odd p) (h: p ∣ a^(2^n) + 1):
  p ≡ 1 [MOD 2^(n+1)] := by


  let d := orderOf (a : ZMod p)

  -- have h1 : a^d ≡ 1 [ZMOD p] := by
  --   unfold d
  --   rw [← ZMod.intCast_eq_intCast_iff]
  --   norm_cast
  --   have := pow_orderOf_eq_one (a : ZMod p)
  --   norm_cast at this

  have h2 : a^(2^n) ≡ -1 [ZMOD p] := by
    apply Int.ModEq.symm
    apply Int.modEq_of_dvd
    simp
    norm_cast

  have h3 : a^(2^(n+1)) ≡ 1 [ZMOD p] := by
    have := Int.ModEq.pow 2 h2
    rw [← pow_mul] at this
    simp at this
    rw [show 2^(n+1) = 2^n * 2 by omega]
    exact this

  have h4 : a^(p-1) ≡ 1 [ZMOD p] := by
    apply Int.ModEq.pow_card_sub_one_eq_one hprime
    rw [Int.coprime_iff_nat_coprime]
    norm_cast
    have := Nat.coprime_or_dvd_of_prime hprime a
    rcases this with h5 | h5
    . rw [Nat.coprime_comm]
      exact h5
    . have : p ∣ a^(2^n) := by
        have := @Nat.pow_dvd_pow 1 (2^n) a (by rw [show 1 = 2^0 by simp]; apply Nat.pow_le_pow_right (by norm_num); omega)
        simp at this
        have := Nat.dvd_trans h5 this
        exact this

      have := @Nat.dvd_sub p (a ^ 2 ^ n + 1) (a ^ 2 ^ n) (by omega) h this
      simp at this
      subst p
      contrapose hprime
      decide

  have h5 : d ∣ 2^(n+1) := by
    unfold d
    apply orderOf_dvd_of_pow_eq_one
    rw [← ZMod.intCast_eq_intCast_iff] at h3
    norm_cast at h3
    norm_cast

  have h6 : d ∣ p-1 := by
    unfold d
    apply orderOf_dvd_of_pow_eq_one
    rw [← ZMod.intCast_eq_intCast_iff] at h4
    norm_cast at h4
    norm_cast

  by_cases h7 : d < 2^(n+1)
  . have h8 : d ∣ 2^n := by
      rw [Nat.dvd_prime_pow (by norm_num)] at h5
      obtain ⟨k, hk1, hk2⟩ := h5
      by_cases hk3 : k = n+1
      . subst k
        rw [hk2] at h7
        simp at h7
      . have hk4 : k ≤ n := by omega
        rw [hk2]
        rw [Nat.pow_dvd_pow_iff_le_right]
        . exact hk4
        . norm_num

    have h9 : a^(2^n) ≡ 1 [ZMOD p] := by
      unfold d at h8
      rw [orderOf_dvd_iff_pow_eq_one] at h8
      rw [← ZMod.intCast_eq_intCast_iff]
      norm_cast at h8
      norm_cast

    apply Int.ModEq.symm at h9
    have h10:= Int.ModEq.trans h9 h2
    apply Int.ModEq.symm at h10
    apply Int.ModEq.dvd at h10
    simp at h10
    norm_cast at h10
    apply Nat.le_of_dvd (by simp) at h10
    interval_cases p
    . omega
    . contrapose hprime
      decide
    . contrapose hodd
      simp

  . have h8 : d = 2^(n+1) := by
      simp at h7
      apply Nat.le_of_dvd (by simp) at h5
      omega

    rw [h8] at h6
    apply Nat.ModEq.symm
    rw [Nat.modEq_iff_dvd']
    . exact h6
    . contrapose hodd
      simp at hodd
      rw [hodd]
      simp

theorem number_theory_612625 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
  n ∣ 2^(m - 1) + 1 ∧ m ∣ 2^(n - 1) + 1 ↔ (m, n) = (1, 1) ∨ (m, n) = (1, 2) ∨ (m, n) = (2, 1):= by
  constructor
  . intro ⟨h1, h2⟩

    by_cases hm1 : 2 < m ∧ 2 < n
    . have hm_odd : Odd m := by
        have : Even (2^(n-1)) := by
          use 2^(n-2)
          rw [← two_mul]
          nth_rw 2 [show 2 = 2^1 by simp]
          rw [← pow_add]
          rw [show 1+(n-2) = n-1 by omega]
        have : Odd (2^(n-1) + 1) := by simp [this]
        contrapose this
        simp at this ⊢
        obtain ⟨k, hk⟩ := this
        obtain ⟨q, hq⟩ := h2
        use k*q
        rw [hq, hk]
        ring

      have hn_odd : Odd n := by
        have : Even (2^(m-1)) := by
          use 2^(m-2)
          rw [← two_mul]
          nth_rw 2 [show 2 = 2^1 by simp]
          rw [← pow_add]
          rw [show 1+(m-2) = m-1 by omega]
        have : Odd (2^(m-1) + 1) := by simp [this]
        contrapose this
        simp at this ⊢
        obtain ⟨k, hk⟩ := this
        obtain ⟨q, hq⟩ := h1
        use k*q
        rw [hq, hk]
        ring

      have := Nat.exists_eq_two_pow_mul_odd (show m-1 ≠ 0 by omega)
      obtain ⟨a, u, h_u_odd, ha⟩ := this
      have := Nat.exists_eq_two_pow_mul_odd (show n-1 ≠ 0 by omega)
      obtain ⟨b, v, h_v_odd, hb⟩ := this

      have h3 : 2^(a+1) ∣ (n-1) := by
        rw [ha] at h1
        rw [pow_mul'] at h1

        have h_prime_mod : ∀ p ∈ n.primeFactors, p ≡ 1 [MOD 2^(a+1)] := by
          intro p h
          simp at h
          have hp : Nat.Prime p := h.1
          have hp1 : Odd p := by
            contrapose hn_odd
            simp at hn_odd
            obtain ⟨k, hk⟩ := hn_odd
            have := h.2.1
            obtain ⟨q, hq⟩ := this
            rw [hk] at hq
            simp
            use k*q
            rw [hq]
            ring

          have hp2 : p ∣ (2 ^ u) ^ 2 ^ a + 1 := Nat.dvd_trans h.2.1 h1
          have := @number_theory_612625_lemma_1 p (2^u) a hp hp1 hp2
          exact this
        have : n ≡ 1 [MOD 2 ^ (a + 1)] := by
          rw [Nat.ModEq]
          simp
          have hn_factorization : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
            nth_rw 3 [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
            rw [Nat.prod_factorization_eq_prod_primeFactors]

          rw [← hn_factorization]
          have := Finset.prod_nat_mod n.primeFactors (2 ^ (a + 1)) (fun x => x ^ n.factorization x)
          rw [this]
          suffices (∏ i ∈ n.primeFactors, i ^ n.factorization i % 2 ^ (a + 1)) = 1 by
            rw [this]
            simp

          apply Finset.prod_eq_one
          intro p hp
          rw [Nat.pow_mod]
          have := h_prime_mod p hp
          rw [Nat.ModEq] at this
          rw [this]
          simp

        apply Nat.ModEq.symm at this
        rw [Nat.modEq_iff_dvd'] at this
        . exact this
        . omega

      have : a+1 ≤ b := by
        rw [hb] at h3
        have : 2 ^ (a + 1) ∣ 2 ^ b := by
          rw [Nat.Coprime.dvd_mul_right] at h3
          . exact h3
          . simp
            exact h_v_odd

        rw [Nat.pow_dvd_pow_iff_le_right] at this
        . exact this
        . norm_num

      have h4 : 2^(b+1) ∣ (m-1) := by
        rw [hb] at h2
        rw [pow_mul'] at h2

        have h_prime_mod : ∀ p ∈ m.primeFactors, p ≡ 1 [MOD 2^(b+1)] := by
          intro p h
          simp at h
          have hp : Nat.Prime p := h.1
          have hp1 : Odd p := by
            contrapose hm_odd
            simp at hm_odd
            obtain ⟨k, hk⟩ := hm_odd
            have := h.2.1
            obtain ⟨q, hq⟩ := this
            rw [hk] at hq
            simp
            use k*q
            rw [hq]
            ring

          have hp2 : p ∣ (2 ^ v) ^ 2 ^ b + 1 := Nat.dvd_trans h.2.1 h2
          have := @number_theory_612625_lemma_1 p (2^v) b hp hp1 hp2
          exact this

        have : m ≡ 1 [MOD 2^(b+1)] := by
          rw [Nat.ModEq]
          simp
          have hm_factorization : ∏ p ∈ m.primeFactors, p ^ m.factorization p = m := by
            nth_rw 3 [← Nat.factorization_prod_pow_eq_self (show m ≠ 0 by omega)]
            rw [Nat.prod_factorization_eq_prod_primeFactors]

          rw [← hm_factorization]
          have := Finset.prod_nat_mod m.primeFactors (2 ^ (b + 1)) (fun x => x ^ m.factorization x)
          rw [this]
          suffices (∏ i ∈ m.primeFactors, i ^ m.factorization i % 2 ^ (b + 1)) = 1 by
            rw [this]
            simp

          apply Finset.prod_eq_one
          intro p hp
          rw [Nat.pow_mod]
          have := h_prime_mod p hp
          rw [Nat.ModEq] at this
          rw [this]
          simp
        apply Nat.ModEq.symm at this
        rw [Nat.modEq_iff_dvd'] at this
        . exact this
        . omega


      have : b+1 ≤ a := by
        rw [ha] at h4
        have : 2 ^ (b + 1) ∣ 2 ^ a := by
          rw [Nat.Coprime.dvd_mul_right] at h4
          . exact h4
          . simp
            exact h_u_odd


        rw [Nat.pow_dvd_pow_iff_le_right] at this
        . exact this
        . norm_num

      omega
    . wlog hm2 : m ≤ 2
      . suffices (n, m) = (1, 1) ∨ (n, m) = (1, 2) ∨ (n, m) = (2, 1) by
          simp
          simp at this
          omega
        apply this n m
        all_goals try assumption
        omega
        simp at hm1 hm2
        exact hm1 hm2

      . interval_cases m
        . simp at h1
          apply Nat.le_of_dvd at h1
          interval_cases n
          all_goals simp
        . by_cases hn1 : n = 1
          . subst n; simp
          . have hn2 : 2 ≤ n := by omega
            have : Even (2^(n-1)) := by
              use 2^(n-2)
              rw [← two_mul]
              nth_rw 2 [show 2 = 2^1 by simp]
              rw [← pow_add]
              rw [show 1+(n-2) = n-1 by omega]
            have : Odd (2^(n-1) + 1) := by simp [this]
            have := Odd.not_two_dvd_nat this
            contradiction

  . rintro (h | h | h)
    all_goals
    . simp at h
      obtain ⟨h1, h2⟩ := h
      subst m n
      simp
