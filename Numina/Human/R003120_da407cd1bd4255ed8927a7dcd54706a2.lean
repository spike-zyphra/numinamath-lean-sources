import Mathlib

/- ## Aufgabe 19/74

Man bestimme alle Lösungen der Gleichung $a^{b}+7=c$, wobei $a, b$ und $c$ Primzahlen sind.

 -/
theorem number_theory_154411 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (h : a^b + 7 = c) :
    a = 2 ∧ b = 2 ∧ c = 11 := by
        --First, observe that c ≥ 7. (indeed the inequality is strict)
        have c_ge_7 : c ≥ 7 := by omega
        --Since c ≥ 7, it cannot be two. So c must be odd.
        have c_odd : Odd c := by
            by_contra c_odd
            have c_even : Even c := by exact Nat.not_odd_iff_even.mp c_odd
            have : c = 2 := by exact (Nat.Prime.even_iff hc).mp c_even
            --This gives the contradiction.
            linarith

        --Since c and 7 are both odd, a cannot be odd.
        have a_even : Even a := by
            by_contra a_even
            have a_odd : Odd a := by exact Nat.not_even_iff_odd.mp a_even
            --Therefore a^b  must be odd as well.
            have a_to_the_b_odd : Odd (a^b) := by
                exact Odd.pow a_odd
            have odd_7 : Odd 7 := by exact Nat.odd_iff.mpr rfl
            --Therefore, since 7 is odd, c must be even.
            have c_even : Even c := by
                rw [←h]
                exact Odd.add_odd a_to_the_b_odd odd_7
            --But we know c is not even, so a contradiction.
            have c_odd : ¬ Even c := by exact Nat.not_even_iff_odd.mpr c_odd
            contradiction

        --Since a is even and prime, a must be 2.
        have a_eq_2 : a = 2 := by exact (Nat.Prime.even_iff ha).mp a_even

        --Now we show that b cannot be odd.
        --We show that a^b cannot be 2 modulo 3.
        have a_b_neq_2_mod_3 : a^b % 3 ≠ 2 := by
            by_contra p
            --we use mod-artithemtic laws at h.
            have : (a^b % 3 + 7 % 3) % 3 = c % 3 := by
                omega
            --So c must be congruent to 0 modulo 3.
            have c_cong_0_mod_3 : c % 3 = 0 := by
                rw [p] at this
                omega
            --This means 3 ∣ c, so c must be 3, which is absurd as c ≥ 7.
            have c_div_by_3 : 3 ∣ c := by exact Nat.dvd_of_mod_eq_zero c_cong_0_mod_3
            have c_eq_3 : c = 3 := by
                --The divisors of c must be 1 and c as c is prime.
                have c_divisors : Nat.divisors c = {1, c} := by exact Nat.Prime.divisors hc
                --Since 3 ≠ 1, 3 must be c.
                have : 3 ∈ Nat.divisors c := by
                    refine Nat.mem_divisors.mpr ?_
                    exact ⟨c_div_by_3, by omega⟩
                have : 3 = 1 ∨ 3 = c := by exact (Nat.dvd_prime hc).mp c_div_by_3
                have : c = 3 := by omega
                exact this
            linarith

        have b_even : Even b := by
            by_contra p
            have b_odd : Odd b := by exact Nat.not_even_iff_odd.mp p
            have contr : a^b % 3 = 2 := by
                rw [a_eq_2]
                obtain ⟨k,hk⟩ := b_odd
                rw [hk]
                have simplify :  2 ^ (2 * k + 1) = (2^2)^k * 2 := by
                    rw [Nat.pow_add, Nat.pow_mul, Nat.pow_one]
                have simplify_pow : (2^2)^k * 2 = 4^k * 2 := by ring
                have take_mod : (4^k * 2) % 3 = (((4^k) % 3) * (2 % 3)) % 3 := by omega
                have simplify4k : (4^k) % 3 = (4 % 3)^k % 3 := by
                    rw [Nat.pow_mod]
                have simplify4mod3 : (4 % 3)^k % 3 = 1 := by norm_num
                have simplify2mod3 : 2 % 3 = 2 := by norm_num

                rw [simplify4mod3] at simplify4k
                rw [simplify4k] at take_mod
                rw [simplify2mod3] at take_mod
                rw [simplify]
                rw [simplify_pow]
                rw [take_mod]

            --This gives 2 ≠ 2 which is a contradiction.
            contradiction

        --Now, since b is even and b is also prime, b must be 2.
        have b_eq_2 : b = 2 := by exact (Nat.Prime.even_iff hb).mp b_even

        --Now we back-substitute and find c.

        rw [a_eq_2, b_eq_2] at h
        simp at h
        have c_eq_11 : c = 11 := by exact h.symm
        --We are done now.
        exact ⟨a_eq_2, b_eq_2, c_eq_11⟩