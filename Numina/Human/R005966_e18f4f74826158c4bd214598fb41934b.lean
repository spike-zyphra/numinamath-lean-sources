import Mathlib
/- A product of five primes is of the form $A B C, A B C$, where $A, B$, and $C$ represent digits. If one of the primes is 491, find the product $A B C, A B C$. -/
theorem number_theory_610929 (A B C p1 p2 p3 p4 p5 : ℕ) (hA : 1 ≤ A ∧ A ≤ 9) (hB : 0 ≤ B ∧ B ≤ 9) (hC : 0 ≤ C ∧ C ≤ 9) (hp1 : Nat.Prime p1) (hp2 : Nat.Prime p2) (hp3 : Nat.Prime p3) (hp4 : Nat.Prime p4) (hp5 : Nat.Prime p5) (h : p1 * p2 * p3 * p4 * p5 = A * 10 ^ 5 + B * 10 ^ 4 + C * 10 ^ 3 + A * 10 ^ 2 + B * 10 ^ 1 + C * 10 ^ 0) (h1 : p1 = 491) : A * 10 ^ 5 + B * 10 ^ 4 + C * 10 ^ 3 + A * 10 ^ 2 + B * 10 ^ 1 + C * 10 ^ 0 = 982982:= by
  -- Simplify the goal and hypothesis
  simp
  simp at h

  -- Rewrite the six-digit number ABC,ABC as 1001 * (A*100 + B*10 + C)
  rw [show A * 100000 + B * 10000 + C * 1000 + A * 100 + B * 10 + C = 1001 * (A * 100 + B * 10 + C) by ring] at h

  -- Substitute p1 with 491
  subst p1

  -- Prove that 491 divides 7*11*13*(A*100 + B*10 + C)
  have h1 : 491 ∣ 7 * 11 * 13 * (A * 100 + B * 10 + C):= by rw [←h] ; rw [show 491 * p2 * p3 * p4 * p5 = 491 * (p2 * p3 * p4 * p5) by ring] ; simp

  -- By the prime divisibility property, either 491 divides 1001 or 491 divides (A*100 + B*10 + C)
  replace h1 : 491 ∣ 1001 ∨ 491 ∣ (A * 100 + B * 10 + C):= by exact (Nat.Prime.dvd_mul hp1).mp h1

  -- Split into two cases based on what 491 divides
  rcases h1 with h1 | h1
  .
    -- Case 1: 491 divides 1001 - this is impossible (contradiction by omega)
    omega
  .
    -- Case 2: 491 divides (A*100 + B*10 + C)
    replace h1 : ∃ k : ℕ, A * 100 + B * 10 + C = 491 * k:= by exact h1
    rcases h1 with ⟨k, h1⟩

    -- Extract the bounds on A, B, and C
    rcases hA with ⟨hA1, hA2⟩
    rcases hB with ⟨hB1, hB2⟩
    rcases hC with ⟨hC1, hC2⟩

    -- Given the constraints on A, B, C, k must be either 1 or 2
    have hk1 : k = 1 ∨ k = 2:= by omega
    rcases hk1 with hk1 | hk1
    .
      -- Case 2.1: k = 1, meaning A*100 + B*10 + C = 491
      subst k
      simp at h1
      rw [h1] at h

      -- This implies p2*p3*p4*p5 = 1001
      replace h : p2 * p3 * p4 * p5 = 1001:= by linarith

      -- 1001 = 7*11*13
      rw [show 1001 = 7 * 11 * 13 by norm_num] at h

      -- Establish that 7, 11, and 13 are prime numbers
      have g1 : Nat.Prime 7:= by norm_num
      have g2 : Nat.Prime 11:= by norm_num
      have g3 : Nat.Prime 13:= by norm_num

      -- All prime factors must be greater than 1
      have g4 : p3 > 1:= by exact Nat.Prime.one_lt hp3
      have g5 : p4 > 1:= by exact Nat.Prime.one_lt hp4
      have g6 : p5 > 1:= by exact Nat.Prime.one_lt hp5
      have g7 : p2 > 1:= by exact Nat.Prime.one_lt hp2

      -- p5 must divide 7*11*13
      replace h1 : p5 ∣ 7 * 11 * 13:= by rw [←h] ; simp
      apply (Nat.Prime.dvd_mul hp5).mp at h1
      rcases h1 with h1 | h1
      .
        -- Case: p5 divides 7*11
        apply (Nat.Prime.dvd_mul hp5).mp at h1
        rcases h1 with h1 | h1
        .
          -- Case: p5 = 7
          apply (Nat.prime_dvd_prime_iff_eq hp5 g1).mp at h1
          subst p5

          -- This implies p2*p3*p4 = 11*13
          replace h : p2 * p3 * p4 = 11 * 13:= by linarith

          -- p4 must divide 11*13
          replace h1 : p4 ∣ 11 * 13:= by rw [←h] ; simp
          apply (Nat.Prime.dvd_mul hp4).mp at h1
          rcases h1 with h1 | h1
          .
            -- Case: p4 = 11
            apply (Nat.prime_dvd_prime_iff_eq hp4 g2).mp at h1
            subst p4

            -- This implies p2*p3 = 13
            replace h : p2 * p3 = 13:= by linarith

            -- p3 must divide 13
            replace h1 : p3 ∣ 13:= by rw [←h] ; simp
            apply (Nat.prime_dvd_prime_iff_eq hp3 g3).mp at h1
            subst p3

            -- Contradiction: p2*13 = 13 implies p2 = 1, but p2 > 1
            linarith
          .
            -- Case: p4 = 13
            apply (Nat.prime_dvd_prime_iff_eq hp4 g3).mp at h1
            subst p4

            -- This implies p2*p3 = 11
            replace h : p2 * p3 = 11:= by linarith

            -- p3 must divide 11
            replace h1 : p3 ∣ 11:= by rw [←h] ; simp
            apply (Nat.prime_dvd_prime_iff_eq hp3 g2).mp at h1
            subst p3

            -- Contradiction: p2*11 = 11 implies p2 = 1, but p2 > 1
            linarith
        .
          -- Case: p5 = 11
          apply (Nat.prime_dvd_prime_iff_eq hp5 g2).mp at h1
          subst p5

          -- This implies p2*p3*p4 = 7*13
          replace h : p2 * p3 * p4 = 7 * 13:= by linarith

          -- p4 must divide 7*13
          replace h1 : p4 ∣ 7 * 13:= by rw [←h] ; simp
          apply (Nat.Prime.dvd_mul hp4).mp at h1
          rcases h1 with h1 | h1
          .
            -- Case: p4 = 7
            apply (Nat.prime_dvd_prime_iff_eq hp4 g1).mp at h1
            subst p4

            -- This implies p2*p3 = 13
            replace h : p2 * p3 = 13:= by linarith

            -- p3 must divide 13
            replace h1 : p3 ∣ 13:= by rw [←h] ; simp
            apply (Nat.prime_dvd_prime_iff_eq hp3 g3).mp at h1
            subst p3

            -- Contradiction: p2*13 = 13 implies p2 = 1, but p2 > 1
            linarith
          .
            -- Case: p4 = 13
            apply (Nat.prime_dvd_prime_iff_eq hp4 g3).mp at h1
            subst p4

            -- This implies p2*p3 = 7
            replace h : p2 * p3 = 7:= by linarith

            -- p3 must divide 7
            replace h1 : p3 ∣ 7:= by rw [←h] ; simp
            apply (Nat.prime_dvd_prime_iff_eq hp3 g1).mp at h1
            subst p3

            -- Contradiction: p2*7 = 7 implies p2 = 1, but p2 > 1
            linarith
      .
        -- Case: p5 = 13
        apply (Nat.prime_dvd_prime_iff_eq hp5 g3).mp at h1
        subst p5

        -- This implies p2*p3*p4 = 7*11
        replace h : p2 * p3 * p4 = 7 * 11:= by linarith

        -- p4 must divide 7*11
        replace h1 : p4 ∣ 7 * 11:= by rw [←h] ; simp
        apply (Nat.Prime.dvd_mul hp4).mp at h1
        rcases h1 with h1 | h1
        .
          -- Case: p4 = 7
          apply (Nat.prime_dvd_prime_iff_eq hp4 g1).mp at h1
          subst p4

          -- This implies p2*p3 = 11
          replace h : p2 * p3 = 11:= by linarith

          -- p3 must divide 11
          replace h1 : p3 ∣ 11:= by rw [←h] ; simp
          apply (Nat.prime_dvd_prime_iff_eq hp3 g2).mp at h1
          subst p3

          -- Contradiction: p2*11 = 11 implies p2 = 1, but p2 > 1
          linarith
        .
          -- Case: p4 = 11
          apply (Nat.prime_dvd_prime_iff_eq hp4 g2).mp at h1
          subst p4

          -- This implies p2*p3 = 7
          replace h : p2 * p3 = 7:= by linarith

          -- p3 must divide 7
          replace h1 : p3 ∣ 7:= by rw [←h] ; simp
          apply (Nat.prime_dvd_prime_iff_eq hp3 g1).mp at h1
          subst p3

          -- Contradiction: p2*7 = 7 implies p2 = 1, but p2 > 1
          linarith
    .
      -- Case 2.2: k = 2, meaning A*100 + B*10 + C = 982
      -- This leads to the solution 982,982
      subst k
      linarith
