import Mathlib

-- Example 9 Find all prime numbers p,q,r that satisfy p^q + q^p = r
theorem number_theory_321661 (p q r : ℕ)(hp : p.Prime)(hq : q.Prime)(hr : r.Prime)(hpq : p ≤ q)(hpqr : p^q + q^p = r) : p = 2 ∧ q = 3 ∧ r = 17 := by
  -- First, establish lower bounds for p and q using the fact that primes are at least 2
  have hpge : p ≥ 2 := by exact Nat.Prime.two_le hp
  have hqge : q ≥ 2 := by exact Nat.Prime.two_le hq

  -- Establish a lower bound for r by showing p^q + q^p ≥ 8
  have hrge : r ≥ 8 := by
    rw[← hpqr]
    -- Show that p^q ≥ 4 by using p ≥ 2 and q ≥ 2
    have : p ^ q ≥ 4 := by
      have : p ^ q ≥ p ^ 2 := by exact Nat.pow_le_pow_of_le hpge hqge
      have : p ^ 2 ≥ 4 := by nlinarith
      linarith
    -- Similarly show that q^p ≥ 4
    have : q ^ p ≥ 4 := by
      have : q ^ p ≥ q ^ 2 := by exact Nat.pow_le_pow_of_le hqge hpge
      have : q ^ 2 ≥ 4 := by nlinarith
      linarith
    linarith

  -- Case analysis: first consider when both p and q are odd
  by_cases hodd : Odd p ∧ Odd q
  · -- If both p and q are odd, then p^q and q^p are both odd
    have hodd1 : Odd (p^q) := Odd.pow hodd.1
    have hodd2 : Odd (q^p) := Odd.pow hodd.2

    -- Sum of two odd numbers is even, so r must be even
    have : Even r := by
      rw [← hpqr]
      exact Odd.add_odd hodd1 hodd2

    -- The only even prime is 2, so r = 2
    have : r = 2 := by exact (Nat.Prime.even_iff hr).mp this

    -- But this contradicts our earlier bound r ≥ 8
    linarith

  -- Case when at least one of p or q is even
  · by_cases hptwo : p = 2
    · -- If p = 2, then our equation becomes 2^q + q^2 = r
      rw [hptwo] at hpqr

      -- Rewrite q^2 as 1 + (q-1)(q+1) to analyze divisibility
      have : 2 ^ q + q ^ 2 = 2 ^ q + 1 + (q-1)*(q+1) := by
        have : q - 1 ≥ 1 := by exact Nat.le_sub_one_of_lt hqge
        calc
          _ = 2 ^ q + 1 + (q^2 -1) := by
            refine Eq.symm (Mathlib.Tactic.Ring.add_pf_add_lt (2 ^ q) ?_)
            refine Nat.add_sub_of_le ?h
            nlinarith
          _ = _ := by
            refine Eq.symm ((fun {m k n} => Nat.add_left_cancel_iff.mpr) ?hh)
            ring_nf
            rw [Nat.sub_one_mul]
            ring_nf
            rw [add_comm]
            refine Nat.sub_add_sub_cancel ?hh.hab ?hh.hcb
            · nlinarith
            · linarith
      rw [this] at hpqr

      -- Consider the case where q ≥ 5
      by_cases hqge5 : q ≥ 5
      · -- Show that 3 divides 2^q + 1 when q is odd
        have h3dvd : 3 ∣ (2 ^ q + 1) := by
          have : 3 = 2 + 1 := by rfl
          rw [this]
          have : 1 = 1 ^ q := by exact Eq.symm (Nat.one_pow q)
          nth_rw 2 [this]
          apply Odd.nat_add_dvd_pow_add_pow 2 1
          -- Since q ≥ 5 and prime, q must be odd
          refine Nat.Prime.odd_of_ne_two hq ?h_two
          linarith

        -- Analyze q modulo 3: there are three possibilities
        have : q % 3 = 0  ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
        rcases this with h1 | h2 | h3

        · -- Case q % 3 = 0: Then q is divisible by 3
          have : 3 ∣ q := by exact Nat.dvd_of_mod_eq_zero h1
          -- Since q is prime and divisible by 3, q = 3
          have : q = 3 := by
            symm
            apply (Nat.dvd_prime_two_le hq (by linarith)).mp this
          -- But this contradicts q ≥ 5
          linarith

        · -- Case q % 3 = 1: Then 3 divides (q-1)
          have : 3 ∣ (q - 1) := by
            refine (Nat.modEq_iff_dvd' ?hhh).mp (id (Eq.symm h2))
            linarith
          -- This implies 3 divides r
          have : 3 ∣ r := by
            rw [← hpqr]
            apply dvd_add h3dvd
            apply dvd_mul_of_dvd_left this
          -- Since r is prime and divisible by 3, r = 3
          have : r = 3 := by
            symm
            apply (Nat.dvd_prime_two_le hr (by linarith)).mp this
          -- But this contradicts r ≥ 8
          linarith

        · -- Case q % 3 = 2: Then 3 divides (q+1)
          have : 3 ∣ (q + 1) := by
            refine Nat.dvd_of_mod_eq_zero ?H
            rw [Nat.add_mod]
            rw [h3]
          -- This implies 3 divides r
          have : 3 ∣ r := by
            rw [← hpqr]
            apply dvd_add h3dvd
            apply dvd_mul_of_dvd_right this
          -- Since r is prime and divisible by 3, r = 3
          have : r = 3 := by
            symm
            apply (Nat.dvd_prime_two_le hr (by linarith)).mp this
          -- But this contradicts r ≥ 8
          linarith

      · -- Case q < 5: Since q is prime, q must be 2, 3, or 4
        simp at hqge5
        have : q = 2 ∨ q = 3 ∨ q = 4 := by omega
        rcases this with h1 | h2 | h3

        · -- If q = 2, calculate r = 2^2 + 2^2 = 4 + 4 = 8
          rw [h1] at hpqr
          simp at hpqr
          -- But 8 is not prime, contradiction
          rw [← hpqr] at hr
          norm_num at hr

        · -- If q = 3, calculate r = 2^3 + 3^2 = 8 + 9 = 17
          rw [h2] at hpqr
          simp at hpqr
          -- This is our solution: p = 2, q = 3, r = 17
          exact ⟨hptwo, ⟨h2, hpqr.symm⟩⟩

        · -- If q = 4, then q is not prime, contradiction
          rw [h3] at hq
          norm_num at hq

    · -- Case p ≠ 2: Since p ≤ q and p is prime, p must be odd
      have hqtwo : ¬ q = 2 := by omega
      have hpodd : Odd p := by exact Nat.Prime.odd_of_ne_two hp hptwo
      have hqodd : Odd q := by exact Nat.Prime.odd_of_ne_two hq hqtwo

      -- But this means both p and q are odd, contradicting our assumption
      have :=  hodd ⟨hpodd, hqodd⟩
      exact False.elim this
