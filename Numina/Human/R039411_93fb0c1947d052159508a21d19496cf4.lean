import Mathlib

/- 4. Find all prime numbers $p$ such that the numbers $4 p^{2}+1$ and $6 p^{2}+1$ are also prime. -/
theorem number_theory_104601 (p : ℕ) (hp : Nat.Prime p) :
    Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1) ↔ p = 5 := by

        --It must be the case that (p % 5 = 0) ∨ (p % 5 = 1) ∨ (p % 5 = 2) ∨ (p % 5 = 3) ∨ (p % 5 = 4).
        have h : (p % 5 = 0) ∨ (p % 5 = 1) ∨ (p % 5 = 2) ∨ (p % 5 = 3) ∨ (p % 5 = 4) := by
            omega
        constructor
        --We do a case analysis.
        by_cases
        --First assume p % 5 = 0.
        h1 : p % 5 = 0
        --Then 5 ∣ p.
        have h1_1 : 5 ∣ p := by
            omega
        --Therefore, since p is prime, p = 5.
        have h1_1_1 : 5 = p := by
            have : Nat.Prime 5 := by decide
            apply (Nat.prime_dvd_prime_iff_eq this hp).mp
            exact h1_1
        intro hyp
        exact h1_1_1.symm

        --Now the other four cases.
        have : (p % 5 = 1) ∨ (p % 5 = 2) ∨ (p % 5 = 3) ∨ (p % 5 = 4) := by
            omega
        by_cases
        --Assume p % 5 = 1.
        h2 : p % 5 = 1
        --Assume Nat.Prime (4 * p ^ 2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1).
        intro h
        --We show ¬ Nat.Prime (4 * p^2 + 1).
        have h1_1 : ¬ Nat.Prime (4 * p^2 + 1) := by
            by_contra h1_1'
            have h1_1_1 : (4 * p^2 + 1) % 5 = 0 := by
                calc
                    _ = ((4 * p^2 % 5) + (1 % 5)) % 5 := by exact Nat.add_mod (4 * p ^ 2) 1 5
                    _ = ((4 % 5) + (1 % 5)) % 5 := by
                        have h_square : p ^ 2 % 5 = 1 := by
                            rw [Nat.pow_two, Nat.mul_mod, h2]
                        have h_mul : 4 * p ^ 2 % 5 = 4 := by
                            rw [Nat.mul_mod, h_square]
                        rw [h_mul]
                    _ = 0 := by omega

            have h1_1_2 : 5 ∣ (4 * p^2 + 1) := by
                omega
            have h1_1_3 : 5 = 4 * p^2 + 1 := by
                have : Nat.Prime 5 := by decide
                apply (Nat.prime_dvd_prime_iff_eq this h.1).mp
                exact h1_1_2
            have : p^2 = 1 := by linarith
            have : p = 1 := by
                exact Nat.eq_one_of_mul_eq_one_left this
            have : p ≠ 1 := by exact Nat.Prime.ne_one hp
            contradiction
        --Now, since the hypothesis of the implication is false, the consequent follows vacuously.
        tauto
        --Now the other three cases.
        have : (p % 5 = 2) ∨ (p % 5 = 3) ∨ (p % 5 = 4) := by omega
        by_cases
        --Assume p % 5 = 2.
        h3 : p % 5 = 2
        --Assume Nat.Prime (4 * p^2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1).
        intro h'
        --We show that  ¬ Nat.Prime (6 * p ^ 2 + 1).
        have h1_1 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
            by_contra h1_1'
            have h1_1_1 : (6 * p ^ 2 + 1) % 5 = 0 := by
                calc
                    _ = ((6 * p^2) % 5 + (1 % 5)) % 5 := by exact Nat.add_mod (6 * p ^ 2) 1 5
                    _ = ((24 % 5) + (1 % 5)) % 5 := by
                        have h_square : p ^ 2 % 5 = 4 := by
                            rw [Nat.pow_two, Nat.mul_mod, h3]
                        have h_mul : 6 * p ^ 2 % 5 = 24 % 5 := by
                            rw [Nat.mul_mod, h_square]
                        rw [h_mul]
                    _ = 0 := by omega

            have h1_1_2 : 5 ∣ (6 * p ^ 2 + 1) := by
                omega
            have h1_1_3 : 5 = 6 * p^2 + 1 := by
                have : Nat.Prime 5 := by decide
                apply (Nat.prime_dvd_prime_iff_eq this h'.2).mp
                exact h1_1_2
            have : 6 * p^2 = 4 := by linarith
            have : 3 ∣ 4 := by omega
            have : ¬ (3 ∣ 4) := by decide
            contradiction
        --Again, since the hypothesis of the implication is false, the consequent follows vacuously.
        tauto
        --Now, the other two cases. Again, we argue as before.
        have : (p % 5 = 3) ∨ (p % 5 = 4) := by omega
        by_cases
        h4 : p % 5 = 3
        intro h''
        have h1_1 : ¬ Nat.Prime (6 * p ^ 2 + 1) := by
            by_contra h1_1'
            have h1_1_1 : (6 * p ^ 2 + 1) % 5 = 0 := by
                calc
                    _ = ((6 * p^2) % 5 + (1 % 5)) % 5 := by exact Nat.add_mod (6 * p ^ 2) 1 5
                    _ = ((54 % 5) + (1 % 5)) % 5 := by
                        have h_square : p ^ 2 % 5 = 4 := by
                            rw [Nat.pow_two, Nat.mul_mod, h4]
                        have h_mul : 6 * p ^ 2 % 5 = 24 % 5 := by
                            rw [Nat.mul_mod, h_square]
                        rw [h_mul]
                    _ = 0 := by omega

            have h1_1_2 : 5 ∣ (6 * p ^ 2 + 1) := by
                omega
            have h1_1_3 : 5 = 6 * p^2 + 1 := by
                have : Nat.Prime 5 := by decide
                apply (Nat.prime_dvd_prime_iff_eq this h''.2).mp
                exact h1_1_2
            have : 6 * p^2 = 4 := by linarith
            have : 3 ∣ 4 := by omega
            have : ¬ (3 ∣ 4) := by decide
            contradiction
        --Since the hypothesis of the implication is false, the consequent follows vacuously.
        tauto
        --Finally, the remaining case. We argue as before.
        have h5 : p % 5 = 4 := by omega
        --Assume Nat.Prime (4 * p^2 + 1) ∧ Nat.Prime (6 * p ^ 2 + 1).
        intro h'''
        have h1_1 : ¬ Nat.Prime (4 * p^2 + 1) := by
            by_contra h1_1'
            have h1_1_1 : (4 * p^2 + 1) % 5 = 0 := by
                calc
                    _ = ((4 * p^2 % 5) + (1 % 5)) % 5 := by exact Nat.add_mod (4 * p ^ 2) 1 5
                    _ = ((4 % 5) + (1 % 5)) % 5 := by
                        have h_square : p ^ 2 % 5 = 1 := by
                            rw [Nat.pow_two, Nat.mul_mod, h5]
                        have h_mul : 4 * p ^ 2 % 5 = 4 := by
                            rw [Nat.mul_mod, h_square]
                        rw [h_mul]
                    _ = 0 := by omega

            have h1_1_2 : 5 ∣ (4 * p^2 + 1) := by
                omega
            have h1_1_3 : 5 = 4 * p^2 + 1 := by
                have : Nat.Prime 5 := by decide
                apply (Nat.prime_dvd_prime_iff_eq this h'''.1).mp
                exact h1_1_2
            have : p^2 = 1 := by linarith
            have : p = 1 := by
                exact Nat.eq_one_of_mul_eq_one_left this
            have : p ≠ 1 := by exact Nat.Prime.ne_one hp
            contradiction
        --Again, since the hypothesis of the implication is false, the consequent follows vacuously.
        tauto

        --Conversely, assume p = 5.
        intro h''''
        constructor
        --Show 4p^2 + 1 is 101, which is a prime.
        have : 4 * p^2 + 1 = 101 := by
            rw [h'''']
            norm_num
        rw [this]
        norm_num
        --Show 6p^2 + 1 is 151, which is a prime.
        have : 6 * p^2 + 1 = 151 := by
            rw [h'''']
            norm_num
        rw [this]
        norm_num