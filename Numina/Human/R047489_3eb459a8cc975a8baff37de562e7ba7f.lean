import Mathlib
/- Find the smallest positive integer $b$ such that $1111_{b}$ ( 1111 in base $b$ ) is a perfect square. If no such $b$ exists, write "No solution". -/
theorem number_theory_609455 : IsLeast {b : ℕ | b > 1 ∧ IsSquare (1 * b ^ 3 + 1 * b ^ 2 + 1 * b + 1 * b ^ 0)} 7:= by
  simp
  constructor
  .
    -- First part: Prove that 7 is in the set (i.e., 1111 in base 7 is a perfect square)
    simp
    simp [IsSquare]
    use 20
  .
    -- Second part: Prove that no smaller value works
    simp [lowerBounds]
    intro b hb h
    simp [IsSquare] at h
    rcases h with ⟨k, hk⟩
    -- Prove that k > 2
    have hk1 : k > 2:= by
      by_contra H
      simp at H
      replace H : k ^ 2 ≤ 2 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
      have g1 : b ^ 3 > 1:= by refine Nat.one_lt_pow (by omega) hb
      have g2 : b ^ 2 > 1:= by refine Nat.one_lt_pow (by omega) hb
      linarith
    -- Factorize the expression b^3 + b^2 + b + 1 as (b^2 + 1)(b + 1)
    rw [show b ^ 3 + b ^ 2 + b + 1 = (b ^ 2 + 1) * (b + 1) by ring] at hk
    -- Convert to integers for easier manipulation
    zify at hk hb
    set c:= (↑b : ℤ) with hc
    clear_value c
    zify
    rw [←hc]
    replace hc : c ≥ 0:= by omega
    -- Split into two cases: c is odd or c is even
    by_cases h1 : Odd c
    .
      -- Case 1: c is odd
      replace h1 : ∃ k : ℤ, c = 2 * k + 1:= by exact h1
      rcases h1 with ⟨t, ht⟩
      subst c
      -- Algebraic manipulations for the odd case
      rw [show (2 * t + 1) ^ 2 + 1 = 2 * (2 * t ^ 2 + 2 * t + 1) by ring] at hk
      rw [show 2 * (2 * t ^ 2 + 2 * t + 1) * (2 * t + 1 + 1) = (2 * t ^ 2 + 2 * t + 1) * (t + 1) * 4 by ring] at hk
      rw [show (↑k : ℤ) * ↑k = ↑k ^ 2 by ring] at hk
      -- Prove that 4 divides k^2
      have h2 : 4 ∣ k ^ 2:= by
        zify
        rw [←hk]
        simp
      -- Therefore 2 divides k^2
      have g1 : Nat.Prime 2:= by norm_num
      replace h2 : 2 ∣ k ^ 2:= by
        have g2 : 2 ∣ 4:= by omega
        exact Nat.dvd_trans g2 h2
      -- By prime divisibility, 2 divides k
      replace h2 : 2 ∣ k:= by exact Nat.Prime.dvd_of_dvd_pow g1 h2
      replace h2 : ∃ s : ℕ, k = 2 * s:= by exact h2
      rcases h2 with ⟨s, hs⟩
      subst k
      simp at hk
      replace hk : (2 * t ^ 2 + 2 * t + 1) * (t + 1) = s ^ 2:= by linarith
      -- Prove that t+1 and 2*t^2 + 2*t + 1 are coprime
      have h1 : Int.gcd (t + 1) (2 * t ^ 2 + 2 * t + 1) = 1:= by
        suffices IsCoprime (t + 1) (2 * t ^ 2 + 2 * t + 1) by exact Int.isCoprime_iff_gcd_eq_one.mp this
        simp [IsCoprime]
        use (-2 * t), 1
        linarith
      -- If product of coprime integers is a square, each factor must be a square
      have h2 : ∃ d : ℤ, t + 1 = d ^ 2 ∨ t + 1 = -d ^ 2:= by exact Int.sq_of_gcd_eq_one h1 (by rw [show (2 * t ^ 2 + 2 * t + 1) * (t + 1) = (t + 1) * (2 * t ^ 2 + 2 * t + 1) by ring] at hk ; exact hk)
      rcases h2 with ⟨d, h2⟩
      rcases h2 with h2 | h2
      .
        -- Case: t + 1 = d^2
        have h3 : Int.gcd (2 * t ^ 2 + 2 * t + 1) (t + 1) = 1:= by
          suffices IsCoprime (2 * t ^ 2 + 2 * t + 1) (t + 1) by exact Int.isCoprime_iff_gcd_eq_one.mp this
          simp [IsCoprime]
          use 1, (-2 * t)
          linarith
        have h4 : ∃ d : ℤ, 2 * t ^ 2 + 2 * t + 1 = d ^ 2 ∨ 2 * t ^ 2 + 2 * t + 1 = -d ^ 2:= by exact Int.sq_of_gcd_eq_one h3 hk
        rcases h4 with ⟨e, h4⟩
        rcases h4 with h4 | h4
        .
          -- Case: 2*t^2 + 2*t + 1 = e^2
          replace h2 : t = d ^ 2 - 1:= by linarith
          subst t
          -- Use absolute values for cleaner expressions
          rw [show d ^ 2 = |d| ^ 2 by exact Eq.symm (sq_abs d)]
          rw [show d ^ 2 = |d| ^ 2 by exact Eq.symm (sq_abs d)] at h4 hc hk
          set D:= |d| with hD
          clear_value D
          replace hD : D ≥ 0:= by rw [hD] ; positivity
          -- Prove that D ≥ 2
          have h5 : D ≥ 2:= by
            by_contra H
            simp at H
            replace H : D = 0 ∨ D = 1:= by omega
            rcases H with H | H
            .
              subst D
              simp at h4 hk
              clear h1 h3
              replace hk : s ^ 2 = 0:= by
                zify
                linarith
              simp at hk
              subst s
              simp at hk1
            .
              subst D
              simp at h4 hk
              replace hk : s ^ 2 = 1:= by zify ; linarith
              replace hk : s = 1:= by exact Nat.eq_one_of_mul_eq_one_left hk
              subst s
              simp at hk1
          replace h5 : D ^ 2 ≥ 2 ^ 2:= by nlinarith only [h5]
          linarith
        .
          -- Case: 2*t^2 + 2*t + 1 = -e^2 (impossible)
          have g1 : e ^ 2 ≥ 0:= by positivity
          replace hc : t ≥ 0:= by omega
          have g2 : 2 * t ^ 2 + 2 * t + 1 > 0:= by positivity
          linarith
      .
        -- Case: t + 1 = -d^2 (impossible)
        have g1 : d ^ 2 ≥ 0:= by positivity
        linarith
    .
      -- Case 2: c is even
      simp at h1
      simp [Even] at h1
      rcases h1 with ⟨r, hr⟩
      ring_nf at hr
      subst c
      simp at hc
      -- Prove that (r*2)^2 + 1 and r*2 + 1 are coprime
      have h1 : Int.gcd ((r * 2) ^ 2 + 1) (r * 2 + 1) = 1:= by
        suffices IsCoprime ((r * 2) ^ 2 + 1) (r * 2 + 1) by exact Int.isCoprime_iff_gcd_eq_one.mp this
        simp [IsCoprime]
        use (-r), (1 + r * (2 * r - 1))
        linarith
      rw [show (↑k : ℤ) * ↑k = ↑k ^ 2 by ring] at hk
      -- If product of coprime integers is a square, each factor must be a square
      have h2 : ∃ d : ℤ, (r * 2) ^ 2 + 1 = d ^ 2 ∨ (r * 2) ^ 2 + 1 = -d ^ 2:= by exact Int.sq_of_gcd_eq_one h1 hk
      rcases h2 with ⟨d, h2⟩
      rcases h2 with h2 | h2
      .
        -- Case: (r*2)^2 + 1 = d^2
        replace h2 : (d - r * 2) * (d + r * 2) = 1:= by linarith
        -- If a number divides 1, it must be 1 or -1
        replace h3 : d - r * 2 = 1 ∨ d - r * 2 = -1:= by exact Int.eq_one_or_neg_one_of_mul_eq_one h2
        rcases h3 with h3 | h3
        .
          rw [h3] at h2
          simp at h2
          linarith
        .
          rw [h3] at h2
          simp at h2
          linarith
      .
        -- Case: (r*2)^2 + 1 = -d^2 (impossible)
        have g1 : d ^ 2 ≥ 0:= by positivity
        have g2 : (r * 2) ^ 2 + 1 > 0:= by positivity
        linarith
