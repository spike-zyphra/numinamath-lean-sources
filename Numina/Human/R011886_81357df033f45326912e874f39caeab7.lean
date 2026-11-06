import Mathlib
/- 5. Find all triples $(m, n, p)$ such that $p^{n}+144=m^{2}$ (where $m, n \in \mathbf{Z}_{+}$, and $p$ is a prime).

---

The translation is provided as requested, maintaining the original formatting and structure. -/
theorem number_theory_299822 : {(m, n, p) : ℕ × ℕ × ℕ | Nat.Prime p ∧ p ^ n + 144 = m ^ 2} = {(13, 2, 5), (20, 8, 2), (15, 4, 3)}:= by
  ext ⟨m, n, p⟩
  constructor
  .
    -- Forward direction: if (m, n, p) satisfies the equation, then it's one of the three solutions
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    -- First, prove that m > 12
    have g1 : m > 12:= by
      by_contra H
      simp at H
      replace H : m ^ 2 ≤ 12 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
      have g1 : p > 1:= by exact Nat.Prime.one_lt h1
      have g1 : p ^ n > 0:= by positivity
      linarith
    -- Substitute k = m - 12 to get k(k + 24) = p^n
    set k:= m - 12 with hk
    clear_value k
    replace hk : m = k + 12:= by omega
    subst m
    replace h2 : k * (k + 24) = p ^ n:= by linarith
    -- Since k divides p^n and p is prime, k must be a power of p
    have h3 : ∃ t : ℕ, t ≤ n ∧ k = p ^ t:= by
      replace h2 : k ∣ p ^ n:= by rw [←h2] ; simp
      exact (Nat.dvd_prime_pow h1).mp h2
    rcases h3 with ⟨t, ht, h3⟩
    -- Set d = n - t, so n = t + d
    set d:= n - t with hd
    clear_value d
    replace hd : n = t + d:= by omega
    subst n
    clear ht g1
    subst k
    -- This gives us p^t + 24 = p^d
    replace h2 : p ^ t + 24 = p ^ d:= by
      rw [show p ^ (t + d) = p ^ t * p ^ d by ring_nf] at h2
      have g1 : p > 1:= by exact Nat.Prime.one_lt h1
      replace g1 : p ^ t > 0:= by positivity
      exact Nat.eq_of_mul_eq_mul_left g1 h2
    -- Case analysis on whether t = 0
    by_cases h3 : t = 0
    .
      -- Case t = 0: then 1 + 24 = p^d, so p^d = 25 = 5^2
      subst t
      simp at h2
      -- Since 5 divides p^d and p is prime, p = 5
      have h3 : p = 5:= by
        replace h2 : 5 ∣ p ^ d:= by rw [←h2] ; omega
        have g1 : Nat.Prime 5:= by decide
        replace h2 : 5 ∣ p:= by exact Nat.Prime.dvd_of_dvd_pow g1 h2
        replace h2 : 5 = p:= by exact (Nat.prime_dvd_prime_iff_eq g1 h1).mp h2
        rw [h2]
      subst p
      -- Since 5^d = 25 = 5^2, we have d = 2
      rw [show 25 = 5 ^ 2 by ring_nf] at h2
      replace h2 : Nat.log 5 (5 ^ 2) = Nat.log 5 (5 ^ d):= by rw [h2]
      rw [Nat.log_pow] at h2
      rw [Nat.log_pow] at h2
      .
        rw [←h2]
        simp
      .
        omega
      .
        omega
    .
      -- Case t > 0: then p^t < p^d, so d > t
      have h4 : d > t:= by
        replace h2 : p ^ t < p ^ d:= by omega
        have g1 : p > 1:= by exact Nat.Prime.one_lt h1
        exact (Nat.pow_lt_pow_iff_right g1).mp h2
      -- Since p divides p^d and p^t + 24 = p^d, p divides 24
      have g1 : p ∣ p ^ d:= by refine dvd_pow_self p (by omega)
      rw [←h2] at g1
      have g2 : p ∣ p ^ t:= by exact dvd_pow_self p h3
      replace g1 : p ∣ 24:= by exact (Nat.dvd_add_iff_right g2).mpr g1
      -- Since 24 = 2^3 * 3, either p divides 2^3 or p divides 3
      rw [show 24 = 2 ^ 3 * 3 by ring_nf] at g1
      replace g1 : p ∣ 2 ^ 3 ∨ p ∣ 3:= by exact (Nat.Prime.dvd_mul h1).mp g1
      rcases g1 with g1 | g1
      .
        -- Case p divides 2^3: then p = 2
        replace g1 : p ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow h1 g1
        have g2 : Nat.Prime 2:= by decide
        replace g1 : p = 2:= by exact (Nat.prime_dvd_prime_iff_eq h1 g2).mp g1
        subst p
        clear g2
        -- Bound on t: 2^t ≤ 24, so t ≤ 4
        have h5 : 2 ^ t ≤ 24:= by
          set e:= d - t with he
          clear_value e
          replace hd : d = t + e:= by omega
          subst d
          replace h4 : t + e ≥ t + 1:= by omega
          clear he
          replace h4 : 2 ^ (t + e) ≥ 2 ^ (t + 1):= by refine Nat.pow_le_pow_of_le_right (by omega) h4
          rw [←h2] at h4
          ring_nf at h4
          linarith
        have h6 : t ≤ 4:= by
          by_contra H
          simp at H
          replace H : t ≥ 5:= by omega
          replace H : 2 ^ t ≥ 2 ^ 5:= by refine Nat.pow_le_pow_of_le_right (by omega) H
          linarith
        -- Check each possible value of t
        replace h6 : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4:= by omega
        rcases h6 with h6 | h6 | h6 | h6
        .
          -- Case t = 1: 2 + 24 = 26, but 26 is not a power of 2
          subst t
          simp at h2
          replace h2 : 13 ∣ 2 ^ d:= by rw [←h2] ; omega
          have g1 : Nat.Prime 13:= by decide
          replace h2 : 13 ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow g1 h2
          omega
        .
          -- Case t = 2: 4 + 24 = 28, but 28 is not a power of 2
          subst t
          simp at h2
          replace h2 : 7 ∣ 2 ^ d:= by rw [←h2] ; omega
          have g1 : Nat.Prime 7:= by decide
          replace h2 : 7 ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow g1 h2
          omega
        .
          -- Case t = 3: 8 + 24 = 32 = 2^5, so d = 5
          subst t
          simp at h2
          rw [show 32 = 2 ^ 5 by ring_nf] at h2
          replace h2 : Nat.log 2 (2 ^ 5) = Nat.log 2 (2 ^ d):= by rw [h2]
          rw [Nat.log_pow] at h2
          rw [Nat.log_pow] at h2
          .
            rw [←h2]
            simp
          .
            omega
          .
            omega
        .
          -- Case t = 4: 16 + 24 = 40, but 40 is not a power of 2
          subst t
          simp at h2
          replace h2 : 5 ∣ 2 ^ d:= by rw [←h2] ; omega
          have g1 : Nat.Prime 5:= by decide
          replace h2 : 5 ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow g1 h2
          omega
      .
        -- Case p divides 3: then p = 3
        replace g2 : Nat.Prime 3:= by decide
        replace g1 : p = 3:= by exact (Nat.prime_dvd_prime_iff_eq h1 g2).mp g1
        subst p
        -- Since 3^t + 24 = 3^d and t > 0, we must have t = 1
        replace h3 : t = 1:= by
          by_contra H
          replace H : t ≥ 2:= by omega
          set e:= d - t with he
          clear_value e
          replace hd : d = t + e:= by omega
          subst d
          set t1:= t - 2 with ht1
          clear_value t1
          replace ht1 : t = t1 + 2:= by omega
          subst t
          ring_nf at h2
          have g1 : 9 ∣ 3 ^ t1 * 3 ^ e * 9:= by simp
          rw [←h2] at g1
          omega
        subst t
        -- With t = 1: 3 + 24 = 27 = 3^3, so d = 3
        simp at h2
        rw [show 27 = 3 ^ 3 by ring_nf] at h2
        replace h2 : Nat.log 3 (3 ^ 3) = Nat.log 3 (3 ^ d):= by rw [h2]
        rw [Nat.log_pow] at h2
        rw [Nat.log_pow] at h2
        .
          rw [←h2]
          simp
        .
          omega
        .
          omega
  .
    -- Backward direction: verify that each of the three solutions satisfies the equation
    intro h
    simp at h
    rcases h with h | h | h
    all_goals
      rcases h with ⟨h1, h2, h3⟩
      subst m n p
      simp
      decide
