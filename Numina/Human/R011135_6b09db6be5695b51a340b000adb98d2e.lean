import Mathlib
/- 6. Find all such prime numbers $p$ and $q$ that $p^{q+1}+q^{p+1}$ is a square of a natural number. -/
theorem number_theory_225048 : {(p, q) : ℕ × ℕ | Nat.Prime p ∧ Nat.Prime q ∧ IsSquare (p ^ (q + 1) + q ^ (p + 1))} = {(2, 2)}:= by
  ext ⟨p, q⟩
  constructor
  .
    -- Forward direction: if (p,q) satisfies the conditions, then (p,q) = (2,2)
    intro h
    simp at h
    rcases h with ⟨h1, h2, h3⟩
    rcases h3 with ⟨n, hn⟩
    rw [show n * n = n ^ 2 by ring] at hn
    -- Key lemma: if p is odd and prime, then p^(q+1) + q^(p+1) cannot be a perfect square
    have h3 : ∀ p q n : ℕ, Odd p → Nat.Prime p → Nat.Prime q → p ^ (q + 1) + q ^ (p + 1) = n ^ 2 → False:= by
      intro p q n h1 hp hq h
      -- First show that p ≠ q
      have hpq : p ≠ q:= by
        by_contra H
        rw [←H] at h
        -- If p = q, then we have 2p^(p+1) = n^2, which leads to a contradiction
        have h3 : Even (n ^ 2):= by
          rw [←h]
          simp
        -- If n^2 is even, then n must be even
        replace h3 : Even n:= by
          by_contra H
          simp at H
          replace H : Odd (n ^ 2):= by exact Odd.pow H
          absurd H
          simp
          exact h3
        rcases h3 with ⟨s, hs⟩
        ring_nf at hs
        set t:= p ^ (p + 1) with ht
        clear_value t
        -- Since p is odd, p^(p+1) is odd
        replace ht : Odd t:= by
          subst t
          refine Odd.pow h1
        subst n
        ring_nf at h
        replace h : t = s ^ 2 * 2:= by omega
        -- This implies 2 divides t, so t is even
        replace h : 2 ∣ t:= by rw [h] ; simp
        replace h : Even t:= by exact (even_iff_exists_two_nsmul t).mpr h
        -- Contradiction: t cannot be both odd and even
        absurd h
        simp
        exact ht
      -- Since p is odd, p = 2k+1 for some k
      rcases h1 with ⟨k, hk⟩
      rw [show p + 1 = (k + 1) * 2 by linarith] at h
      rw [show q ^ ((k + 1) * 2)  = (q ^ (k + 1)) ^ 2 by ring] at h
      -- Both p and q are greater than 1 since they are prime
      have hp1 : p > 1:= by exact Nat.Prime.one_lt hp
      have hq1 : q > 1:= by exact Nat.Prime.one_lt hq
      -- n > q^(k+1) since p^(q+1) > 0
      have h3 : n > q ^ (k + 1):= by
        suffices n ^ 2 > (q ^ (k + 1)) ^ 2 by exact lt_of_pow_lt_pow_left' 2 this
        suffices p ^ (q + 1) > 0 by linarith
        positivity
      -- Let m = n - q^(k+1)
      set m:= n - q ^ (k + 1) with hm
      clear_value m
      replace hm : n = m + q ^ (k + 1):= by omega
      subst n
      -- Substituting gives us m(m + 2q^(k+1)) = p^(q+1)
      replace h : m * (m + 2 * q ^ (k + 1)) = p ^ (q + 1):= by linarith
      -- We claim that m = 1
      have h4 : m = 1:= by
        -- Since m divides p^(q+1) and p is prime, m must be a power of p
        have h4 : ∃ t : ℕ, t ≤ q + 1 ∧ m = p ^ t:= by
          replace h : m ∣ p ^ (q + 1):= by rw [←h] ; simp
          exact (Nat.dvd_prime_pow hp).mp h
        rcases h4 with ⟨t, ht, h4⟩
        -- Similarly, m + 2q^(k+1) must also be a power of p
        have h5 : ∃ s : ℕ, s ≤ q + 1 ∧ m + 2 * q ^ (k + 1) = p ^ s:= by
          replace h : m + 2 * q ^ (k + 1) ∣ p ^ (q + 1):= by rw [←h] ; simp
          exact (Nat.dvd_prime_pow hp).mp h
        rcases h5 with ⟨s, _, h5⟩
        -- Since m + 2q^(k+1) > m, we have s > t
        have h6 : s > t:= by
          suffices p ^ s > p ^ t by exact (Nat.pow_lt_pow_iff_right hp1).mp this
          suffices q ^ (k + 1) > 0 by linarith
          positivity
        -- Case analysis on whether t = 0
        by_cases h7 : t = 0
        .
          -- If t = 0, then m = 1
          subst t
          simp at h4
          exact h4
        .
          -- If t > 0, we derive a contradiction showing p = q
          absurd hpq
          subst m
          -- p divides p^s
          have h8 : p ∣ p ^ s:= by refine dvd_pow_self p (by omega)
          rw [←h5] at h8
          -- p divides p^t
          have h9 : p ∣ p ^ t:= by refine dvd_pow_self p h7
          -- Therefore p divides 2q^(k+1)
          replace h8 : p ∣ 2 * q ^ (k + 1):= by exact (Nat.dvd_add_iff_right h9).mpr h8
          -- Since p is odd, gcd(p,2) = 1
          have h10 : Nat.Coprime p 2:= by refine Nat.coprime_two_right.mpr (by subst p ; simp)
          -- Therefore p divides q^(k+1)
          replace h8 : p ∣ q ^ (k + 1):= by exact Nat.Coprime.dvd_of_dvd_mul_left h10 h8
          -- Since p is prime and divides q^(k+1), p divides q
          replace h8 : p ∣ q:= by exact Nat.Prime.dvd_of_dvd_pow hp h8
          -- Since both p and q are prime, p = q
          exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h8
      subst m
      simp at h
      -- Now we have 1 + 2q^(k+1) = p^(q+1), which forces q = 2
      have h4 : q = 2:= by
        by_contra H
        -- If q ≠ 2, then q is odd
        replace H : Odd q:= by exact Nat.Prime.odd_of_ne_two hq H
        have H1:= H
        rcases H1 with ⟨q1, hq1⟩
        -- q^(k+1) is odd
        replace H : Odd (q ^ (k + 1)):= by exact Odd.pow H
        rcases H with ⟨s, hs⟩
        rw [hs] at h
        -- p is odd
        replace hk : Odd p:= by subst p ; simp
        -- p^(q+1) is odd
        replace hk : Odd (p ^ (q1 + 1)):= by exact Odd.pow hk
        rw [show q + 1 = (q1 + 1) * 2 by omega] at h
        rw [show p ^ ((q1 + 1) * 2) = (p ^ (q1 + 1)) ^ 2 by ring] at h
        rcases hk with ⟨t, ht⟩
        rw [ht] at h
        ring_nf at h
        -- This leads to 4 dividing 2, which is impossible
        replace h : 2 + s * 4 = 4 * (t + t ^ 2):= by omega
        replace h : 4 ∣ 2 + s * 4:= by rw [h] ; simp
        have g1 : 4 ∣ s * 4:= by simp
        replace h : 4 ∣ 2:= by exact (Nat.dvd_add_iff_left g1).mpr h
        omega
      subst q
      ring_nf at h
      subst p
      -- With q = 2 and p = 2k+1, we get 2^(k+1) = k * (complicated expression)
      replace h : 2 ^ (k + 1) = k * (2 * (2 * k + 1) * (k + 1) + 1):= by ring_nf ; linarith
      set A:= 2 * (2 * k + 1) * (k + 1) + 1 with hA
      clear_value A
      -- A > 1
      have hA1 : A > 1:= by
        subst A
        simp
      -- A is odd
      replace hA : Odd A:= by
        use (2 * k + 1) * (k + 1)
        linarith
      -- A must be a power of 2
      replace h : ∃ u : ℕ, u ≤ k + 1 ∧ A = 2 ^ u:= by
        replace h : A ∣ 2 ^ (k + 1):= by rw [h] ; simp
        exact (Nat.dvd_prime_pow hq).mp h
      rcases h with ⟨u, hu, h⟩
      -- Since A is odd, u must be 0
      replace hu : u = 0:= by
        by_contra H
        set u1:= u - 1 with hu1
        clear_value u1
        replace hu1 : u = u1 + 1:= by omega
        subst u
        ring_nf at h
        -- If u > 0, then A is even, contradicting that A is odd
        replace h : 2 ∣ A:= by rw [h] ; simp
        replace h : Even A:= by exact (even_iff_exists_two_nsmul A).mpr h
        absurd h
        simp
        exact hA
      subst u
      simp at h
      -- This gives A = 1, which contradicts A > 1
      linarith
    simp
    -- Apply the lemma to show no solution exists unless both p and q are 2
    by_contra H
    simp at H
    by_cases h4 : p ≠ 2
    .
      -- If p ≠ 2, then p is odd, so we get a contradiction
      replace h4 : Odd p:= by exact Nat.Prime.odd_of_ne_two h1 h4
      exact h3 p q n h4 h1 h2 hn
    .
      -- If p = 2 but q ≠ 2, then q is odd, so we get a contradiction by symmetry
      simp at h4
      replace H:= H h4
      replace H : Odd q:= by exact Nat.Prime.odd_of_ne_two h2 H
      exact h3 q p n H h2 h1 (by linarith)
  .
    -- Backward direction: (2,2) satisfies the conditions
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    subst p q
    simp
    -- 2 is prime and 2^3 + 2^3 = 16 = 4^2 is a perfect square
    refine ⟨by decide, by use 4⟩
