import Mathlib
/- 26. Find all positive integers $m, n$ and prime $p$ such that $\binom{m}{2}-1=p^{\mathrm{n}}$ holds. -/
theorem number_theory_321988 : {(m, n, p) : ℕ × ℕ × ℕ | m > 0 ∧ n > 0 ∧ p > 0 ∧ p.Prime ∧ (m.choose 2 - 1 = p ^ n)} = {(3, 1, 2), (4, 1, 5), (5, 2, 3), (8, 3, 3)}:= by
  ext ⟨m, n, p⟩
  constructor
  .
    -- Forward direction: if (m,n,p) satisfies the conditions, then it's one of the four solutions
    intro h
    simp at h
    rcases h with ⟨h1, h2, h3, h4, h5⟩
    -- Since p is prime, we have p > 1
    have h6 : p > 1:= by exact Nat.Prime.one_lt h4
    -- p^n is positive
    have g1 : p ^ n > 0:= by positivity
    -- Rewrite the equation as 2 * C(m,2) = 2 * p^n + 2
    replace h5 : 2 * m.choose 2 = 2 * p ^ n + 2:= by omega
    -- Use the formula C(m,2) = m(m-1)/2
    rw [Nat.choose_two_right m] at h5
    -- Show that 2 * (m * (m-1) / 2) = m * (m-1)
    have g2 : 2 * (m * (m - 1) / 2)  = m * (m - 1):= by
      set M:= m - 1 with hM
      clear_value M
      replace hM : m = M + 1:= by omega
      subst m
      -- Case analysis on whether M is odd or even
      by_cases hM1 : Odd M
      .
        -- Case: M is odd
        rcases hM1 with ⟨k, hk⟩
        subst M
        ring_nf
        rw [show 2 + k * 6 + k ^ 2 * 4 = 2 * (2 * k ^ 2 + 3 * k + 1) by ring]
        simp
        ring
      .
        -- Case: M is even
        simp at hM1
        rcases hM1 with ⟨k, hk⟩
        subst M
        ring_nf
        rw [show k * 2 + k ^ 2 * 4 = 2 * (2 * k ^ 2 + k) by ring]
        simp
        ring
    rw [g2] at h5
    -- Case analysis on whether m is odd or even
    by_cases h7 : Odd m
    .
      -- Case: m is odd, so m = 2k + 1 for some k
      rcases h7 with ⟨k, hk⟩
      subst m
      rw [show 2 * k + 1 - 1 = 2 * k by omega] at h5
      -- k must be positive
      have hkpos : k > 0:= by
        by_contra H
        simp at H
        subst k
        simp at h5
      -- Let l = k - 1, so k = l + 1
      set l:= k - 1 with hl
      clear_value l
      replace hl : k = l + 1:= by omega
      subst k
      clear g2
      ring_nf at h5
      -- We get (l + 2)(2l + 1) = p^n
      replace h5 : (l + 2) * (2 * l + 1) = p ^ n:= by linarith
      by_cases hl : l = 0
      .
        -- Subcase: l = 0, so we have 2 * 3 = p^n, which gives p = 2, n = 1
        subst l
        simp at h5
        have g2 : Nat.Prime 2:= by decide
        replace h5 : p ^ n = 2:= by rw [h5]
        replace h5 : p = 2 ∧ n = 1:= by exact (Nat.Prime.pow_eq_iff g2).mp h5
        rcases h5 with ⟨h5, h6⟩
        subst n p
        simp
      .
        -- Subcase: l > 0, use prime factorization
        -- Since p^n = (l+2)(2l+1), we have l+2 = p^t for some t ≤ n
        have g2 : ∃ t : ℕ, t ≤ n ∧ l + 2 = p ^ t:= by
          replace h5 : l + 2 ∣ p ^ n:= by rw [←h5] ; simp
          exact (Nat.dvd_prime_pow h4).mp h5
        rcases g2 with ⟨t, ht, g2⟩
        -- Let s = n - t, so n = s + t
        set s:= n - t with hs
        clear_value s
        replace hs : n = s + t:= by omega
        subst n
        rw [g2] at h5
        -- This gives us 2l + 1 = p^s
        replace h5 : 2 * l + 1 = p ^ s:= by
          have g3 : p ^ t > 0:= by positivity
          suffices p ^ t * (2 * l + 1) = p ^ t * p ^ s by exact Nat.eq_of_mul_eq_mul_left g3 this
          ring_nf at h5 ⊢
          linarith
        -- s must be positive
        have hs : s > 0:= by
          by_contra H
          simp at H
          subst s
          simp at h5
          trivial
        -- t must be positive
        replace ht : t > 0:= by
          by_contra H
          simp at H
          subst t
          simp at g2
        -- Since p divides both l+2 and 2l+1, and gcd(l+2, 2l+1) divides 3, we get p = 3
        replace h6 : p = 3:= by
          replace h5 : p ∣ 2 * l + 1:= by rw [h5] ; refine dvd_pow_self p (by omega)
          replace g2 : p ∣ l + 2:= by rw [g2] ; refine dvd_pow_self p (by omega)
          replace g2 : p ∣ 2 * (l + 2):= by exact Dvd.dvd.mul_left g2 2
          rw [show 2 * (l + 2) = 2 * l + 1 + 3 by ring] at g2
          replace g2 : p ∣ 3:= by exact (Nat.dvd_add_iff_right h5).mpr g2
          have g3 : Nat.Prime 3:= by decide
          exact (Nat.prime_dvd_prime_iff_eq h4 g3).mp g2
        subst p
        -- With p = 3, we have 2 * 3^t = 3^s + 3
        replace g2 : 2 * 3 ^ t = 3 ^ s + 3:= by linarith
        by_cases g3 : t = 1
        .
          -- Subcase: t = 1, which gives s = 2
          subst t
          simp at g2
          replace g2 : Nat.log 3 (3 ^ s) = Nat.log 3 (3 ^ 1):= by rw [g2] ; simp
          rw [Nat.log_pow] at g2
          rw [Nat.log_pow] at g2
          subst s
          simp
          linarith
          all_goals
            simp
        .
          by_cases g4 : s = 1
          .
            -- Subcase: s = 1, which gives t = 1 (contradiction)
            subst s
            simp at g2
            replace g2 : 3 ^ t = 3 ^ 1:= by linarith
            replace g2 : Nat.log 3 (3 ^ t) = Nat.log 3 (3 ^ 1):= by rw [g2]
            rw [Nat.log_pow] at g2
            rw [Nat.log_pow] at g2
            trivial
            all_goals
              simp
          .
            -- Subcase: s ≥ 2 and t ≥ 2, which leads to a contradiction
            set T:= t - 2 with hT
            set S:= s - 2 with hS
            clear_value T S
            replace ht : t = T + 2:= by omega
            replace hs : s = S + 2:= by omega
            subst t s
            ring_nf at g2
            rw [show 3 ^ T * 18 = 3 ^ T * 2 * 9 by ring] at g2
            replace g2 : 9 ∣ 3 + 3 ^ S * 9:= by rw [←g2] ; simp
            have g3 : 9 ∣ 3 ^ S * 9:= by simp
            replace g2 : 9 ∣ 3:= by exact (Nat.dvd_add_iff_left g3).mpr g2
            omega
    .
      -- Case: m is even, so m = 2k + 2 for some k (since m > 0)
      simp at h7
      set M:= m - 1 with hM
      clear_value M
      replace hM : m = M + 1:= by omega
      subst m
      -- Since m is even, M must be odd
      replace h7 : Odd M:= by
        by_contra H
        simp at H
        replace H : Odd (M + 1):= by exact Even.add_one H
        absurd H
        simp
        exact h7
      clear g2
      -- M = 2k + 1 for some k
      rcases h7 with ⟨k, hk⟩
      subst M
      ring_nf at h5
      -- We get (2k + 3) * k = p^n
      replace h5 : (2 * k + 3) * k = p ^ n:= by linarith
      -- Since p^n = (2k + 3) * k, we have 2k + 3 = p^t for some t ≤ n
      replace g1 : ∃ t : ℕ, t ≤ n ∧ 2 * k + 3 = p ^ t:= by
        replace h5 : 2 * k + 3 ∣ p ^ n:= by rw [←h5] ; simp
        exact (Nat.dvd_prime_pow h4).mp h5
      rcases g1 with ⟨t, ht, g1⟩
      -- Let s = n - t, so n = s + t
      set s:= n - t with hs
      clear_value s
      replace hs : n = s + t:= by omega
      subst n
      rw [g1] at h5
      -- This gives us k = p^s
      replace h5 : k = p ^ s:= by
        have g2 : p ^ t > 0:= by positivity
        suffices p ^ t * k = p ^ t * p ^ s by exact Nat.eq_of_mul_eq_mul_left g2 this
        ring_nf at h5 ⊢
        linarith
      -- k must be nonzero
      replace h3 : k ≠ 0:= by
        by_contra H
        subst k
        replace h6 : p ^ s > 0:= by positivity
        linarith
      by_cases g3 : s = 0
      .
        -- Subcase: s = 0, so k = 1 and 2k + 3 = 5 = p^t
        subst s
        simp at h5
        subst k
        simp at g1
        replace g1 : p ^ t = 5:= by linarith
        have g4 : Nat.Prime 5:= by decide
        replace g1 : p = 5 ∧ t = 1:= by exact (Nat.Prime.pow_eq_iff g4).mp g1
        rcases g1 with ⟨g1, g2⟩
        subst p t
        simp
      .
        -- Subcase: s > 0, use similar argument as before
        -- t must be positive
        replace h3 : t ≠ 0:= by
          by_contra H
          subst t
          simp at g1
        subst k
        -- Since p divides both p^s and 2p^s + 3, and gcd(p^s, 2p^s + 3) divides 3, we get p = 3
        replace h1 : p = 3:= by
          have h2 : p ∣ 2 * p ^ s + 3:= by rw [g1] ; refine dvd_pow_self p (by omega)
          have h3 : p ∣ p ^ s:= by refine dvd_pow_self p (by omega)
          replace h3 : p ∣ 2 * p ^ s:= by exact Dvd.dvd.mul_left h3 2
          have g1 : Nat.Prime 3:= by decide
          suffices p ∣ 3 by exact (Nat.prime_dvd_prime_iff_eq h4 g1).mp this
          exact (Nat.dvd_add_iff_right h3).mpr h2
        subst p
        by_cases g2 : s = 1
        .
          -- Subcase: s = 1, which gives t = 2
          subst s
          simp at g1
          replace g1 : Nat.log 3 (3 ^ t) = Nat.log 3 (3 ^ 2):= by rw [←g1] ; simp
          rw [Nat.log_pow] at g1
          rw [Nat.log_pow] at g1
          subst t
          simp
          all_goals
            simp
        .
          by_cases g4 : t = 1
          .
            -- Subcase: t = 1, which is impossible
            subst t
            simp at g1
          .
            -- Subcase: s ≥ 2 and t ≥ 2, which leads to a contradiction
            set T:= t - 2 with hT
            set S:= s - 2 with hS
            clear_value T S
            replace ht : t = T + 2:= by omega
            replace hs : s = S + 2:= by omega
            subst t s
            ring_nf at g1
            have g5 : 9 ∣ 3 ^ T * 9:= by simp
            rw [←g1] at g5
            omega
  .
    -- Backward direction: each of the four solutions satisfies the conditions
    intro h
    simp at h
    rcases h with h | h | h | h
    all_goals
      rcases h with ⟨h1, h2, h3⟩
      subst m n p
      simp
    .
      -- Verify (3, 1, 2): C(3,2) - 1 = 3 - 1 = 2 = 2^1
      decide
    all_goals
      -- Verify the remaining cases by computation
      refine ⟨by decide, ?_⟩
      simp [Nat.choose_two_right]
