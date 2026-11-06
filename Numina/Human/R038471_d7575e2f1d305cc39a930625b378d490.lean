import Mathlib

/- 8. [7] Let $p, q, r$ be primes such that $2 p+3 q=6 r$. Find $p+q+r$. -/
theorem number_theory_178871 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime) (h : 2 * p + 3 * q = 6 * r) :
    p + q + r = 7 := by

        --First, show that q = 2.
        have h₁ : q = 2 := by
            --Rearrange the equality `h`.
            have h1 : 3 * q = 6 * r - 2 * p := by
                exact Eq.symm (Nat.sub_eq_of_eq_add' (id (Eq.symm h)))
            --Subject 3 * q from `h1`.
            have h2 : 3 * q = 2 * (3 * r - p) := by
                have : 6 * r - 2 * p = 2 * (3 * r - p) := by
                    rw [Nat.mul_sub_left_distrib]
                    ring_nf
                rw [this] at h1
                exact h1
            --Show that 2 ∣ 3 * q using `h2`.
            have h3 : 2 ∣ 3 * q := by
                use (3 * r - p)
            have h_coprime : Nat.Coprime 2 3 := by decide
            --Since 2 and 3 are coprime, 2 must divide q, so q is even. The only even prime is 2.
            have h2q : 2 ∣ q := Nat.Coprime.dvd_of_dvd_mul_left h_coprime h3
            refine (Nat.Prime.even_iff ?_).mp ?_
            exact hpqr.2.1
            exact (even_iff_exists_two_nsmul q).mpr h2q

        --Second, show that p = 3.
        have h₂ : p = 3 := by
            --Rearrange the equality `h`.
            have h1 : 2 * p = 6 * r - 3 * q := by
                exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm h)))
            --Subject 2 * p from `h1`.
            have h2 : 2 * p = 3 * (2 * r - q) := by
                rw [Nat.mul_sub_left_distrib]
                ring_nf
                rw [mul_comm, mul_comm r 6, mul_comm q 3]
                exact h1
            --Show that 3 ∣ 2 * p using `h2`.
            have h3 : 3 ∣ 2 * p := by
                use (2 * r - q)
            have h_coprime : Nat.Coprime 3 2 := by decide
            --Since 2 and 3 are coprime, 3 must divide p.
            --Obtain p = 3.
            have h2p : 3 ∣ p := Nat.Coprime.dvd_of_dvd_mul_left h_coprime h3
            have prime_3 : Nat.Prime 3 := by decide
            exact
              Eq.symm
                ((fun {p q} pp qp ↦ (Nat.prime_dvd_prime_iff_eq pp qp).mp) prime_3 hpqr.1 h2p)
        --Finally, find r, and hence p + q + r.
        rw [h₁] at h
        rw [h₂] at h
        have h₃ : r = 2 := by
            linarith
        rw [h₁, h₂, h₃]