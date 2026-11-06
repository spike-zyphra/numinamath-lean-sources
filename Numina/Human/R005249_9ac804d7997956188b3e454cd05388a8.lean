import Mathlib
/- Déterminer tous les entiers $x$ tels que $2^{x}+x^{2}+25$ est le cube d'un nombre premier. -/
theorem number_theory_607146 (x : ℕ) : (∃ p : ℕ, p.Prime ∧ (2 ^ x + x ^ 2 + 25) = p ^ 3) ↔ x = 6:= by
    -- We'll prove the equivalence in both directions
    constructor
    .
        -- Forward direction: if 2^x + x^2 + 25 = p^3 for some prime p, then x = 6
        intro h
        rcases h with ⟨p, hp, h⟩
        -- First, we prove that p ≠ 2
        have h1 : p ≠ 2:= by
            by_contra H
            subst p
            simp at h
        -- Since p is prime and not 2, p must be odd
        replace h1 : Odd p:= by exact Nat.Prime.odd_of_ne_two hp h1
        -- We'll prove that x must be even
        have h2 : Even x:= by
            by_contra H
            simp at H
            have h2 : x ≠ 0:= by exact Nat.ne_of_odd_add H
            have g1 : Even 2:= by decide
            replace g1 : Even (2 ^ x):= by exact (Nat.even_pow' h2).mpr g1
            have g2 : Odd 25:= by decide
            replace H : Odd (x ^ 2):= by exact Odd.pow H
            replace H : Odd (2 ^ x + x ^ 2):= by exact Even.add_odd g1 H
            replace H : Even (2 ^ x + x ^ 2 + 25):= by exact Odd.add_odd H g2
            rw [h] at H
            replace h1 : Odd (p ^ 3):= by exact Odd.pow h1
            absurd H
            simp
            exact h1
        -- Since x is even, we can write x = 2y for some natural number y
        replace h2 : ∃ y : ℕ, x = y + y:= by exact h2
        rcases h2 with ⟨y, hy⟩
        ring_nf at hy
        subst x
        -- Case analysis: either y = 0 or y > 0
        by_cases hy : y = 0
        .
            -- Case y = 0, so x = 0
            subst y
            simp at h
            -- We'll show that p must be between 2 and 3, which is impossible
            have hp1 : p > 2:= by
                by_contra H
                simp at H
                replace H : p ^ 3 ≤ 2 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
                linarith
            have hp2 : p < 3:= by
                by_contra H
                simp at H
                replace H : p ^ 3 ≥ 3 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
                linarith
            linarith
        .
            -- Case y > 0
            replace hy : y ≥ 1:= by omega
            -- We'll prove that p ≠ 3
            have h2 : p ≠ 3:= by
                by_contra H
                subst p
                simp at h
                replace hy : y * 2 ≥ 2:= by omega
                replace hy : (y * 2) ^ 2 ≥ 2 ^ 2:= by exact Nat.pow_le_pow_of_le_left hy 2
                have g1 : 2 ^ (y * 2) > 0:= by positivity
                linarith
            -- Simplify the equation
            ring_nf at h
            rw [show y * 2 = 2 * y by ring] at h
            rw [show 2 ^ (2 * y) = (2 ^ 2) ^ y by exact Nat.pow_mul 2 2 y] at h
            ring_nf at h
            -- Modular arithmetic analysis: y^2 mod 3
            have h3 : y ^ 2 ≡ 1 [MOD 3] ∨ y ^ 2 ≡ 0 [MOD 3]:= by
                mod_cases y % 3
                all_goals
                    apply Nat.ModEq.pow 2 at H
                    simp at H
                    aesop
            rcases h3 with h3 | h3
            .
                -- Case: y^2 ≡ 1 (mod 3)
                replace h3 : y ^ 2 * 4 ≡ 1 * 4 [MOD 3]:= by exact Nat.ModEq.mul h3 rfl
                simp at h3
                have h4 : 4 ≡ 1 [MOD 3]:= by rfl
                replace h4 : 4 ^ y ≡ 1 ^ y [MOD 3]:= by exact Nat.ModEq.pow y h4
                simp at h4
                replace h3 : 25 + y ^ 2 * 4 ≡ 25 + 4 [MOD 3]:= by exact Nat.ModEq.add_left 25 h3
                simp at h3
                replace h3 : 25 + y ^ 2 * 4 + 4 ^ y ≡ 29 + 1 [MOD 3]:= by exact Nat.ModEq.add h3 h4
                simp at h3
                rw [h] at h3
                replace h3 : p ^ 3 ≡ 0 [MOD 3]:= by exact h3
                replace h3 : 3 ∣ p ^ 3:= by exact Nat.dvd_of_mod_eq_zero h3
                have g1 : Nat.Prime 3:= by norm_num
                replace h3 : 3 ∣ p:= by exact Nat.Prime.dvd_of_dvd_pow g1 h3
                replace h3 : 3 = p:= by exact (Nat.prime_dvd_prime_iff_eq g1 hp).mp h3
                rw [←h3] at h2
                trivial
            .
                -- Case: y^2 ≡ 0 (mod 3)
                replace h3 : 3 ∣ y ^ 2:= by exact Nat.dvd_of_mod_eq_zero h3
                have g1 : Nat.Prime 3:= by norm_num
                replace h3 : 3 ∣ y:= by exact Nat.Prime.dvd_of_dvd_pow g1 h3
                replace h3 : ∃ z : ℕ, y = 3 * z:= by exact h3
                rcases h3 with ⟨z, hz⟩
                subst y
                replace hy : z > 0:= by omega
                -- Case analysis on z
                by_cases hz : z = 1
                .
                    -- Case z = 1, so y = 3 and x = 6
                    subst z
                    simp
                .
                    -- Case z ≥ 2
                    replace hz : z ≥ 2:= by omega
                    clear hy
                    rw [show 3 * z = z * 3 by ring] at h
                    rw [show 4 ^ (z * 3) = (4 ^ z) ^ 3 by exact Nat.pow_mul 4 z 3] at h
                    -- We'll prove that 4^z < p < 4^z + 1, which is impossible
                    have hp1 : p > 4 ^ z:= by
                        by_contra H
                        simp at H
                        replace H : p ^ 3 ≤ (4 ^ z) ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
                        rw [←h] at H
                        have g1 : (z * 3) ^ 2 ≥ 0:= by positivity
                        linarith
                    have hp2 : p < 4 ^ z + 1:= by
                        by_contra H
                        simp at H
                        replace H : p ^ 3 ≥ (4 ^ z + 1) ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
                        rw [show (4 ^ z + 1) ^ 3 = (4 ^ z) ^ 3 + 3 * (4 ^ z) ^ 2 * 1 + 3 * (4 ^ z) * 1 ^ 2 + 1 ^ 3 by ring] at H
                        simp at H
                        rw [←h] at H
                        have g2 : 4 ^ z ≥ 4 ^ 2:= by refine Nat.pow_le_pow_of_le_right (by omega) hz
                        have g3 : 4 ^ z ≥ 6 * z:= by
                            set w:= z - 1 with hw
                            have h1 : z = w + 1:= by omega
                            clear_value w
                            subst z
                            ring_nf
                            have g3:= one_add_mul_le_pow (show -2 ≤ 3 by omega) w
                            ring_nf at g3
                            zify
                            simp at hz
                            zify at hz
                            linarith
                        replace g3 : (4 ^ z) ^ 2 ≥ (6 * z) ^ 2:= by exact Nat.pow_le_pow_of_le_left g3 2
                        have g4 : z ^ 2 ≥ 0:= by positivity
                        linarith
                    linarith
    .
        -- Backward direction: if x = 6, then 2^x + x^2 + 25 = p^3 for some prime p
        intro h
        subst x
        -- We'll show that p = 5 works
        use 5
        norm_num
