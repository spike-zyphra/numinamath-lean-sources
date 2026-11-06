import Mathlib


/- ## Task 2 - 190922
The numbers in a triplet $(p, q, r)$ are called "Prime Triplets" if and only if each of the three numbers $p, q, r$ is a prime number and if $p, q, r$ are three consecutive odd numbers in this order.

Prove that there is exactly one triplet $(p, q, r)$ that satisfies all these conditions! -/

theorem number_theory_178410 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : q = p + 2) (hqr : r = q + 2) :
    (p, q, r) = (3, 5, 7) := by
  mod_cases h : p % 3
  · -- If p is divisible by 3, then it must be equal to 3.
    rw [Nat.modEq_zero_iff_dvd, Nat.dvd_prime hp] at h
    simp only [OfNat.ofNat_ne_one, false_or] at h
    -- Substituting p = 3 into the equations for q and r, we get q = 5 and r = 7.
    rw [hqr, hpq, h.symm]
  · -- If p ≡ 1 (mod 3), then q must be divisible by 3, so q = 3.
    have : 3 ∣ q := by apply Nat.dvd_of_mod_eq_zero; rw [hpq, Nat.add_mod]; rw_mod_cast [h]
    simp only [Nat.dvd_prime hq, OfNat.ofNat_ne_one, false_or] at this
    simp only [← this, Nat.reduceEqDiff] at hpq
    -- But then p = 1, which is not prime.
    rw [hpq] at hp
    contradiction
  · -- If p ≡ 2 (mod 3), then r must be divisible by 3, so r = 3.
    have : 3 ∣ r := by apply Nat.dvd_of_mod_eq_zero; rw [hqr, hpq, add_assoc, Nat.add_mod]; rw_mod_cast [h]; norm_num
    simp only [Nat.dvd_prime hr, OfNat.ofNat_ne_one, false_or] at this
    simp only [← this, Nat.reduceEqDiff] at hqr
    -- But then q = 1, which is not prime.
    rw [hqr] at hq
    contradiction