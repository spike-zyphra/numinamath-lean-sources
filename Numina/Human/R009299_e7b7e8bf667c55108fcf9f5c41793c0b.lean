import Mathlib
/- Trouver tous les nombres premiers $p, q$ vérifiant $p^{5}+p^{3}+2=q^{2}-q$. -/
theorem number_theory_607429 : {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ p ^ 5 + p ^ 3 + 2 = q ^ 2 - q} = {(2, 7), (3, 17)}:= by
    ext ⟨p, q⟩
    constructor
    -- Forward direction: if (p,q) satisfies the conditions, then it must be (2,7) or (3,17)
    .
        intro h
        rcases h with ⟨hp, hq, h⟩
        -- Prove that q cannot be 2
        have hq1 : q ≠ 2:= by
            by_contra H
            subst q
            simp at h
            have hp1 : p > 1:= by exact Nat.Prime.one_lt hp
            linarith
        -- Since q is prime and not 2, q must be at least 3
        replace hq2 : q ≥ 2:= by exact Nat.Prime.two_le hq
        replace hq1 : q ≥ 3:= by omega
        clear hq2
        -- Rewrite the equation in a more convenient form
        replace h : p ^ 3 * (p ^ 2 + 1) + 2 = q ^ 2 - q:= by rw [←h] ; ring_nf
        replace h : p ^ 3 * (p ^ 2 + 1) = q ^ 2 - q - 2:= by omega
        -- Factor the right side of the equation
        have h1 : q ^ 2 - q - 2 = (q - 2) * (q + 1):= by
            set t:= q - 2 with ht
            clear_value t
            replace ht : q = t + 2:= by omega
            subst q
            ring_nf
            omega
        rw [h1] at h
        clear h1
        -- Case analysis: p = 3 or p ≠ 3
        by_cases hp1 : p = 3
        -- Case 1: p = 3
        .
            subst p
            simp at h
            set t:= q - 2 with ht
            clear_value t
            replace ht : q = t + 2:= by omega
            subst q
            zify at h
            replace h : ((↑t : ℤ) - 15) * (t + 18) = 0:= by linarith
            simp at h
            rcases h with h | h
            -- Subcase: t = 15, which means q = 17
            .
                replace h : t = 15:= by omega
                subst t
                simp
            -- Subcase: t + 18 = 0, which is impossible since q ≥ 3
            .
                zify at hq1
                linarith
        -- Case 2: p ≠ 3
        .
            -- p^3 divides (q-2)*(q+1)
            have h1 : p ^ 3 ∣ (q - 2) * (q + 1):= by rw [←h] ; simp
            -- Calculate gcd(q-2, q+1) using properties of gcd
            have h2 : Nat.gcd (q - 2) (q + 1) = Nat.gcd (q - 2) (q + 1 - (q - 2)):= by refine Eq.symm (Nat.gcd_sub_self_right (by omega))
            rw [show q + 1 - (q - 2) = 3 by omega] at h2
            have h3 : Nat.gcd (q - 2) 3 ∣ 3:= by exact Nat.gcd_dvd_right (q - 2) 3
            rw [←h2] at h3
            -- Prove that p is coprime to gcd(q-2, q+1)
            replace h2 : Nat.Coprime p ((q - 2).gcd (q + 1)):= by
                have g1 : Nat.Prime 3:= by norm_num
                replace h3 : Nat.gcd (q - 2) (q + 1) = 1 ∨ Nat.gcd (q - 2) (q + 1) = 3:= by exact (Nat.dvd_prime g1).mp h3
                rcases h3 with h3 | h3
                .
                    rw [h3]
                    simp
                .
                    rw [h3]
                    exact (Nat.coprime_primes hp g1).mpr hp1
            -- Prove that p is coprime to at least one of (q-2) or (q+1)
            replace h2 : Nat.Coprime p (q - 2) ∨ Nat.Coprime p (q + 1):= by
                by_contra H
                simp at H
                rcases H with ⟨H1, H2⟩
                have H3 : Nat.gcd p (q - 2) ∣ p:= by exact Nat.gcd_dvd_left p (q - 2)
                have H4 : Nat.gcd p (q + 1) ∣ p:= by exact Nat.gcd_dvd_left p (q + 1)
                replace H3 : Nat.gcd p (q - 2) = 1 ∨ Nat.gcd p (q - 2) = p:= by exact (Nat.dvd_prime hp).mp H3
                replace H4 : Nat.gcd p (q + 1) = 1 ∨ Nat.gcd p (q + 1) = p:= by exact (Nat.dvd_prime hp).mp H4
                simp [H1] at H3
                simp [H2] at H4
                replace H1 : p ∣ q - 2:= by rw [←H3] ; exact Nat.gcd_dvd_right p (q - 2)
                replace H2 : p ∣ q + 1:= by rw [←H4] ; exact Nat.gcd_dvd_right p (q + 1)
                have H5 : p ∣ Nat.gcd (q - 2) (q + 1):= by exact Nat.dvd_gcd H1 H2
                replace h2 : Nat.gcd p (Nat.gcd (q - 2) (q + 1)) = 1:= by exact h2
                have H6 : p ∣ p:= by simp
                replace H6 : p ∣ p.gcd ((q - 2).gcd (q + 1)):= by exact Nat.dvd_gcd H6 H5
                rw [h2] at H6
                simp at H6
                have H7 : p > 1:= by exact Nat.Prime.one_lt hp
                linarith
            -- Split into two subcases based on which factor is coprime to p
            rcases h2 with h2 | h2
            -- Subcase: p is coprime to (q-2)
            .
                replace h2 : Nat.Coprime (p ^ 3) (q - 2):= by exact Nat.Coprime.pow_left 3 h2
                replace h1 : p ^ 3 ∣ q + 1:= by exact Nat.Coprime.dvd_of_dvd_mul_left h2 h1
                replace h1 : ∃ k : ℕ, q + 1 = p ^ 3 * k:= by exact h1
                rcases h1 with ⟨k, hk⟩
                rw [hk] at h
                -- Derive equation p^2 + 1 = (q-2) * k
                replace h : p ^ 2 + 1 = (q - 2) * k:= by
                    zify
                    zify at h
                    set t:= q - 2 with ht
                    clear_value t
                    replace h : (↑p : ℤ) ^ 3 * (p ^ 2 + 1 - t * k) = 0:= by linarith
                    simp at h
                    rcases h with h | h
                    .
                        have H:= Nat.Prime.one_lt hp
                        linarith
                    .
                        linarith
                have hk1 : k ≥ 1:= by
                    by_contra H
                    simp at H
                    subst k
                    simp at hk
                have h4 : p ^ 3 * k ≥ p ^ 3:= by exact Nat.le_mul_of_pos_right (p ^ 3) hk1
                rw [←hk] at h4
                have h5 : (q - 2) * k ≥ q - 2:= by exact Nat.le_mul_of_pos_right (q - 2) hk1
                rw [←h] at h5
                replace h4 : p ^ 3 ≤ p ^ 2 + 4:= by omega
                have hp2 : p ≥ 2:= by exact Nat.Prime.two_le hp
                -- Further case analysis: p = 2 or p ≠ 2
                by_cases hp3 : p = 2
                -- If p = 2, show that q = 7
                .
                    subst p
                    simp at h hk
                    replace h : q - 2 ∣ 5:= by rw [h] ; simp
                    have g1 : Nat.Prime 5:= by norm_num
                    replace h : q - 2 = 1 ∨ q - 2 = 5:= by exact (Nat.dvd_prime g1).mp h
                    rcases h with h | h
                    .
                        replace h : q = 3:= by omega
                        subst q
                        simp at hk
                        replace hk : 8 ∣ 4:= by rw [hk] ; simp
                        omega
                    .
                        replace h : q = 7:= by omega
                        subst q
                        simp
                -- If p ≥ 3, derive a contradiction
                .
                    replace hp2 : p ≥ 3:= by omega
                    replace hp3 : p * p ^ 2 ≥ 3 * p ^ 2:= by exact Nat.mul_le_mul_right (p ^ 2) hp2
                    rw [show p * p ^ 2 = p ^ 3 by ring_nf] at hp3
                    replace hp2 : p ^ 2 ≥ 3 ^ 2:= by exact Nat.pow_le_pow_of_le_left hp2 2
                    linarith
            -- Subcase: p is coprime to (q+1)
            .
                replace h2 : Nat.Coprime (p ^ 3) (q + 1):= by exact Nat.Coprime.pow_left 3 h2
                replace h1 : p ^ 3 ∣ q - 2:= by exact Nat.Coprime.dvd_of_dvd_mul_right h2 h1
                apply Nat.le_of_dvd (by omega) at h1
                have h4 : q + 1 ≥ p ^ 3 + 1:= by omega
                replace h1 : (q - 2) * (q + 1) ≥ p ^ 3 * (p ^ 3 + 1):= by exact Nat.mul_le_mul h1 h4
                rw [←h] at h1
                have hp2 : p > 1:= by exact Nat.Prime.one_lt hp
                have g1 : p ^ 3 > 0:= by positivity
                replace h1 : p ^ 2 + 1 ≥ p ^ 3 + 1:= by exact Nat.le_of_mul_le_mul_left h1 g1
                replace g1 : p ^ 2 > 0:= by positivity
                have hp3 : p * p ^ 2 > p ^ 2:= by exact (Nat.lt_mul_iff_one_lt_left g1).mpr hp2
                ring_nf at hp3
                linarith
    -- Backward direction: verify that (2,7) and (3,17) satisfy the conditions
    .
        intro h
        simp at h
        rcases h with h | h
        all_goals
            rcases h with ⟨hp, hq⟩
            subst p q
            simp
            norm_num
