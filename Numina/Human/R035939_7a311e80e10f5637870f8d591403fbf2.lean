import Mathlib

/- ## Task B-1.3.

Solve the equation in the set of prime numbers


$$

2 p^{3}-q^{2}=2(p+q)^{2}

$$
 -/
theorem number_theory_235030 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : (2 : ℤ) * p ^ 3 - q ^ 2 = 2 * (p + q) ^ 2) : (p, q) = (3, 2) := by
--We first prove that q=2.
  have q2 : q = 2 := by
  --q must be even since it is equal to 2 times a natural number.
    have : (q : ℤ) ^ 2 = 2 * p  ^ 3 - 2 * (p + q) ^ 2 := by
      rw [← h]
      omega
    have : (2 : ℤ) ∣ q ^ 2 := by
      use p ^ 3 - (p + q) ^ 2
      rw [this]
      omega
    apply Prime.dvd_of_dvd_pow (by simp; exact Nat.prime_two) at this
  --So we obtain that 2 divides q.
    have : 2 ∣ q := by
      exact_mod_cast this
  --Since q is prime, it must be equal to 2.
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hq] at this
    rw [this]
  subst q2
--We can now replace q with 2 in the equation and simplify it.
  have new_eq : (2 : ℤ) * (p ^ 3 - p ^ 2 - 4 * p - 6) = 0 := by
    ring_nf
    rw [← sub_eq_zero] at h
    ring_nf at h
    exact h
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at new_eq
  rw [sub_eq_zero] at new_eq
--We have that p divides the left-hand side of the equation, which is equal to 6. So p must divide 6.
  have : (p : ℤ) ∣ p ^ 3 - p ^ 2 - 4 * p := by
    use p ^ 2 - p - 4
    ring_nf
  obtain ⟨k, hk⟩ := this
  rw [hk] at new_eq
  have : p ∣ 6 := by
    zify
    use k
    rw [new_eq]
--Since 6=2*3 and p is prime, we have either p=2 or p=3.
  rw [(by omega: 6 = 2 * 3), Nat.Prime.dvd_mul hp] at this
  rcases this with h2 | h3
--If p=2, the equation is not satisfied.
  · rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at h2
    subst h2
    omega
--If p=3, we find the only solution to the equation, that is p=3 and q=2.
  · rw [Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] at h3
    subst h3
    rfl