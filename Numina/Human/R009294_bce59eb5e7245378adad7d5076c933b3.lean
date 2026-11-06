import Mathlib
/- The number $989 \cdot 1001 \cdot 1007+320$ can be written as the product of three distinct primes $p, q, r$ with $p< q< r$. Find $(p, q, r)$. -/
theorem number_theory_609179 (p q r : ℕ) : (p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ p * q * r = 989 * 1001 * 1007 + 320) ↔ p = 991 ∧ q = 997 ∧ r = 1009:= by
  constructor
  .
    intro h
    rcases h with ⟨hp, hq, hr, h, h2, h3⟩
    -- First, simplify the right side of the equation to 991 * 997 * 1009
    replace h3 : p * q * r = 991 * 997 * 1009:= by linarith
    -- Prove that 991, 997, and 1009 are prime numbers
    have g1 : Nat.Prime 991:= by norm_num
    have g2 : Nat.Prime 997:= by norm_num
    have g3 : Nat.Prime 1009:= by norm_num
    -- Show that 1009 divides p * q * r
    have g4 : 1009 ∣ p * q * r:= by rw [h3] ; omega
    -- Apply the prime divisibility property: if a prime divides a product, it divides at least one factor
    apply (Nat.Prime.dvd_mul g3).mp at g4
    -- Case analysis: either 1009 divides p*q or 1009 divides r
    rcases g4 with g4 | g4
    -- Case 1: 1009 divides p*q
    .
      -- Apply the prime divisibility property again: either 1009 divides p or 1009 divides q
      apply (Nat.Prime.dvd_mul g3).mp at g4
      rcases g4 with g4 | g4
      -- Case 1.1: 1009 divides p
      .
        -- If a prime divides another prime, they must be equal
        replace g4 : 1009 = 1 ∨ 1009 = p:= by exact (Nat.dvd_prime hp).mp g4
        -- Simplify: 1 is not prime, so 1009 = p
        simp at g4
        -- Substitute p = 1009 into the original equation
        rw [←g4] at h3
        -- Simplify the equation to q * r = 991 * 997
        replace h3 : q * r = 991 * 997:= by linarith
        -- Since q < r and p = 1009, we have r > 1009
        replace h2 : r > p:= by omega
        -- This implies q * r > p * p
        replace h2 : q * r > p * p:= by exact Nat.mul_lt_mul_of_lt_of_lt h h2
        -- Substitute p = 1009
        rw [←g4] at h2
        -- Derive a contradiction using linear arithmetic
        by_contra _
        linarith
      -- Case 1.2: 1009 divides q
      .
        -- If a prime divides another prime, they must be equal
        replace g4 : 1009 = 1 ∨ 1009 = q:= by exact (Nat.dvd_prime hq).mp g4
        -- Simplify: 1 is not prime, so 1009 = q
        simp at g4
        -- Substitute q = 1009 into the original equation
        rw [←g4] at h3
        -- Simplify the equation to p * r = 991 * 997
        replace h3 : p * r = 991 * 997:= by linarith
        -- Show that 997 divides p * r
        have g5 : 997 ∣ p * r:= by rw [h3] ; omega
        -- Apply the prime divisibility property: either 997 divides p or 997 divides r
        apply (Nat.Prime.dvd_mul g2).mp at g5
        rcases g5 with g5 | g5
        -- Case 1.2.1: 997 divides p
        .
          -- If a prime divides another prime, they must be equal
          replace g5 : 997 = 1 ∨ 997 = p:= by exact (Nat.dvd_prime hp).mp g5
          -- Simplify: 1 is not prime, so 997 = p
          simp at g5
          -- Substitute p = 997 into the equation
          rw [←g5] at h3
          -- Derive a contradiction using linear arithmetic
          by_contra _
          linarith
        -- Case 1.2.2: 997 divides r
        .
          -- If a prime divides another prime, they must be equal
          replace g5 : 997 = 1 ∨ 997 = r:= by exact (Nat.dvd_prime hr).mp g5
          -- Simplify: 1 is not prime, so 997 = r
          simp at g5
          -- Substitute r = 997 into the equation
          rw [←g5] at h3
          -- Derive a contradiction using linear arithmetic
          by_contra _
          linarith
    -- Case 2: 1009 divides r
    .
      -- If a prime divides another prime, they must be equal
      replace g4 : 1009 = 1 ∨ 1009 = r:= by exact (Nat.dvd_prime hr).mp g4
      -- Simplify: 1 is not prime, so 1009 = r
      simp at g4
      -- Substitute r = 1009 into the original equation
      rw [←g4] at h3
      -- Simplify the equation to p * q = 991 * 997
      replace h3 : p * q = 991 * 997:= by linarith
      -- Show that 997 divides p * q
      have g5 : 997 ∣ p * q:= by rw [h3] ; omega
      -- Apply the prime divisibility property: either 997 divides p or 997 divides q
      apply (Nat.Prime.dvd_mul g2).mp at g5
      rcases g5 with g5 | g5
      -- Case 2.1: 997 divides p
      .
        -- If a prime divides another prime, they must be equal
        replace g5 : 997 = 1 ∨ 997 = p:= by exact (Nat.dvd_prime hp).mp g5
        -- Simplify: 1 is not prime, so 997 = p
        simp at g5
        -- Substitute p = 997 into the equation
        rw [←g5] at h3
        -- Derive a contradiction using linear arithmetic
        by_contra _
        linarith
      -- Case 2.2: 997 divides q
      .
        -- If a prime divides another prime, they must be equal
        replace g5 : 997 = 1 ∨ 997 = q:= by exact (Nat.dvd_prime hq).mp g5
        -- Simplify: 1 is not prime, so 997 = q
        simp at g5
        -- Substitute q = 997 into the equation
        rw [←g5] at h3
        -- Construct the final answer: p = 991, q = 997, r = 1009
        refine ⟨?_ , ?_ , ?_⟩
        all_goals
          linarith
  .
    intro h
    -- Simplify the equation to p * q * r = 991 * 997 * 1009
    rcases h with ⟨g1, g2, g3⟩
    -- Show that p, q, and r are prime numbers
    subst p q r
    -- Show that p < q < r
    norm_num
