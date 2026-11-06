import Mathlib
/- Find all triples $(p, q, r)$ of prime numbers such that all of the following numbers are integers

$$
\frac{p^{2}+2 q}{q+r}, \quad \frac{q^{2}+9 r}{r+p}, \quad \frac{r^{2}+3 p}{p+q}
$$ -/
theorem number_theory_606144 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime) :
((∃ k : ℕ, ((p : ℝ) ^ 2 + 2 * q) / (q + r) = k) ∧ (∃ m : ℕ, ((q : ℝ) ^ 2 + 9 * r) / (r + p) = m) ∧ (∃ n : ℕ, ((r : ℝ) ^ 2 + 3 * p) / (p + q) = n)) ↔ p = 2 ∧ q = 3 ∧ r = 7:= by
    constructor
    -- Forward direction: if all expressions are integers, then p=2, q=3, r=7
    .
        intro h
        rcases h with ⟨⟨k, hk⟩, ⟨m, hm⟩, ⟨n, hn⟩⟩
        rcases hpqr with ⟨hp, hq, hr⟩
        -- Establish that all primes are positive
        have g1:= Nat.Prime.pos hp
        have g2:= Nat.Prime.pos hq
        have g3:= Nat.Prime.pos hr
        rify at g1 g2 g3
        field_simp at hk hm hn
        -- Rewrite the expressions as integer equations
        replace hk : p ^ 2 + 2 * q = k * (q + r):= by rify ; linarith
        replace hm : q ^ 2 + 9 * r = m * (r + p):= by rify ; linarith
        replace hn : r ^ 2 + 3 * p = n * (p + q):= by rify ; linarith
        clear g1 g2 g3
        -- Case analysis: first check if r = 2
        by_cases g1 : r = 2
        .
            -- Subcase: r = 2
            by_cases g2 : p = 2
            .
                -- Subcase: r = 2 and p = 2
                subst r p
                simp at hk hm hn
                rw [show 10 = 2 * 5 by ring] at hn
                -- Analyze divisibility in the third equation
                have g1 : 5 ∣ n * (2 + q):= by rw [←hn] ; omega
                have g2 : Nat.Prime 5:= by decide
                replace g1 : 5 ∣ n ∨ 5 ∣ 2 + q:= by exact (Nat.Prime.dvd_mul g2).mp g1
                rcases g1 with g1 | g1
                .
                    -- Subcase: 5 divides n
                    replace g1 : ∃ t : ℕ, n = 5 * t:= by exact g1
                    rcases g1 with ⟨t, ht⟩
                    subst n
                    replace hn : 2 = t * (2 + q):= by linarith
                    replace hn : 2 + q ∣ 2:= by exact Dvd.intro_left t (id (Eq.symm hn))
                    replace hn : 2 + q = 1 ∨ 2 + q = 2:= by exact (Nat.dvd_prime hr).mp hn
                    simp at hn
                    have g3:= Nat.Prime.pos hq
                    rcases hn with hn | hn
                    all_goals
                        linarith
                .
                    -- Subcase: 5 divides 2+q
                    replace g1 : ∃ t : ℕ, 2 + q = 5 * t:= by exact g1
                    rcases g1 with ⟨t, ht⟩
                    rw [ht] at hn
                    replace hn : 2 = t * n:= by linarith
                    have g1 : t ∣ 2:= by rw [hn] ; simp
                    replace g1 : t = 1 ∨ t = 2:= by exact (Nat.dvd_prime hr).mp g1
                    rcases g1 with g1 | g1
                    .
                        -- Subcase: t = 1
                        subst t
                        simp at ht
                        replace ht : q = 3:= by omega
                        subst q
                        simp at hm
                        replace hm : 4 ∣ 27:= by exact Dvd.intro_left m (id (Eq.symm hm))
                        omega
                    .
                        -- Subcase: t = 2
                        subst t
                        simp at ht
                        replace ht : q = 8:= by omega
                        subst q
                        omega
            .
                -- Subcase: r = 2 but p ≠ 2
                replace h2 : Odd p:= by exact Nat.Prime.odd_of_ne_two hp g2
                subst r
                simp at hn
                -- Prove that q must be 2
                have g1 : q = 2:= by
                    by_contra H
                    replace H : Odd q:= by exact Nat.Prime.odd_of_ne_two hq H
                    replace H : Even (p + q):= by exact Odd.add_odd h2 H
                    replace H : 2 ∣ p + q:= by exact even_iff_two_dvd.mp H
                    replace H : 2 ∣ n * (p + q):= by exact Dvd.dvd.mul_left H n
                    rw [←hn] at H
                    rw [show 4 + 3 * p = 2 * (2 + p) + p by omega] at H
                    have g3 : 2 ∣ 2 * (2 + p):= by omega
                    replace g3 : 2 ∣ p:= by exact (Nat.dvd_add_iff_right g3).mpr H
                    replace g3 : 2 = 1 ∨ 2 = p:= by exact (Nat.dvd_prime hp).mp g3
                    simp at g3
                    rw [←g3] at h2
                    trivial
                subst q
                simp at hk
                -- Analyze divisibility in the first equation
                rw [show k * 4 = 2 * (k * 2) by ring] at hk
                have g1 : 2 ∣ 2 * (k * 2):= by omega
                rw [←hk] at g1
                have g2 : 2 ∣ 4:= by omega
                replace g2 : 2 ∣ p ^ 2:= by exact (Nat.dvd_add_iff_left g2).mpr g1
                replace g2 : 2 ∣ p:= by exact Nat.Prime.dvd_of_dvd_pow hr g2
                replace g2 : 2 = 1 ∨ 2 = p:= by exact (Nat.dvd_prime hp).mp g2
                simp at g2
                rw [←g2] at h2
                trivial
        .
            -- Case: r ≠ 2
            by_cases g2 : q = 2
            .
                -- Subcase: q = 2 but r ≠ 2
                subst q
                -- Prove that p must be 2
                have g2 : p = 2:= by
                    by_contra H
                    replace H : Odd p:= by exact Nat.Prime.odd_of_ne_two hp H
                    have g2 : Odd r:= by exact Nat.Prime.odd_of_ne_two hr g1
                    replace H : Even (r + p):= by exact Odd.add_odd g2 H
                    replace H : 2 ∣ r + p:= by exact even_iff_two_dvd.mp H
                    replace H : 2 ∣ m * (r + p):= by exact Dvd.dvd.mul_left H m
                    rw [←hm] at H
                    simp at H
                    have g3 : 2 ∣ 2 * (2 + 4 * r):= by omega
                    rw [show 4 + 9 * r = 2 * (2 + 4 * r) + r by ring] at H
                    replace H : 2 ∣ r:= by exact (Nat.dvd_add_iff_right g3).mpr H
                    replace H : 2 = 1 ∨ 2 = r:= by exact (Nat.dvd_prime hr).mp H
                    simp at H
                    rw [←H] at g1
                    simp at g1
                subst p
                by_contra _
                simp at hn
                -- Analyze divisibility in the third equation
                rw [show n * 4 = 2 * (n * 2) by ring] at hn
                have g3 : 2 ∣ 2 * (n * 2):= by omega
                rw [←hn] at g3
                have g2 : 2 ∣ 6:= by omega
                replace g2 : 2 ∣ r ^ 2:= by exact (Nat.dvd_add_iff_left g2).mpr g3
                replace g2 : 2 ∣ r:= by exact Nat.Prime.dvd_of_dvd_pow hq g2
                replace g2 : 2 = 1 ∨ 2 = r:= by exact (Nat.dvd_prime hr).mp g2
                simp at g2
                rw [←g2] at g1
                simp at g1
            .
                -- Subcase: q ≠ 2 and r ≠ 2
                -- Establish that both q and r are odd
                have g3 : Odd q:= by exact Nat.Prime.odd_of_ne_two hq g2
                have g4 : Odd r:= by exact Nat.Prime.odd_of_ne_two hr g1
                have g5 : Even (q + r):= by exact Odd.add_odd g3 g4
                replace g5 : 2 ∣ q + r:= by exact even_iff_two_dvd.mp g5
                replace g5 : 2 ∣ k * (q + r):= by exact Dvd.dvd.mul_left g5 k
                rw [←hk] at g5
                -- Prove that p must be 2
                have g6 : 2 ∣ 2 * q:= by omega
                replace g5 : 2 ∣ p ^ 2:= by exact (Nat.dvd_add_iff_left g6).mpr g5
                replace g5 : 2 ∣ p:= by exact Nat.Prime.dvd_of_dvd_pow (by decide) g5
                replace g5 : 2 = 1 ∨ 2 = p:= by exact (Nat.dvd_prime hp).mp g5
                simp at g5
                rw [←g5] at hk
                simp at hk
                -- Prove that k = 1
                have hk1 : k = 1:= by
                    have hk2 : k ≠ 0:= by
                        by_contra H
                        subst k
                        simp at hk
                    by_contra H
                    replace H : k ≥ 2:= by omega
                    have hr1 : r > 1:= by exact Nat.Prime.one_lt hr
                    replace hr1 : r ≥ 3:= by omega
                    replace H : k * (q + r) ≥ 2 * (q + r):= by exact Nat.mul_le_mul_right (q + r) H
                    linarith
                subst k
                simp at hk
                -- Determine the value of r in terms of q
                replace hk : r = q + 4:= by omega
                subst r
                replace g5 : p = 2:= by rw [g5]
                subst p
                simp at hm hn
                -- Analyze divisibility in the third equation
                rw [show (q + 4) ^ 2 + 6 = (2 + q) * (q + 6) + 10 by ring_nf] at hn
                replace hn : 2 + q ∣ (2 + q) * (q + 6) + 10:= by rw [hn] ; simp
                have g5 : 2 + q ∣ (2 + q) * (q + 6):= by simp
                replace hn : 2 + q ∣ 10:= by exact (Nat.dvd_add_iff_right g5).mpr hn
                replace hn : ∃ t : ℕ, 10 = (2 + q) * t:= by exact hn
                rcases hn with ⟨t, ht⟩
                rw [show 10 = 2 * 5 by ring] at ht
                have g6 : 2 ∣ (2 + q) * t:= by rw [←ht] ; omega
                replace g6 : 2 ∣ 2 + q ∨ 2 ∣ t:= by exact (Nat.Prime.dvd_mul hp).mp g6
                rcases g6 with g6 | g6
                .
                    -- Subcase: 2 divides 2+q
                    have g7 : 2 ∣ 2:= by omega
                    replace g6 : 2 ∣ q:= by exact (Nat.dvd_add_iff_right g7).mpr g6
                    replace g3 : ¬(2 ∣ q):= by exact Odd.not_two_dvd_nat g3
                    by_contra _
                    trivial
                .
                    -- Subcase: 2 divides t
                    replace g6 : ∃ s : ℕ, t = 2 * s:= by exact g6
                    rcases g6 with ⟨s, hs⟩
                    subst t
                    replace ht : 5 = (2 + q) * s:= by linarith
                    replace ht : 2 + q ∣ 5:= by rw [ht] ; simp
                    have g8 : 2 + q = 1 ∨ 2 + q = 5:= by exact (Nat.dvd_prime (by decide)).mp ht
                    rcases g8 with g8 | g8
                    .
                        -- Subcase: 2+q = 1 (impossible)
                        by_contra _
                        omega
                    .
                        -- Subcase: 2+q = 5, which means q = 3
                        refine ⟨?_, ?_, ?_⟩
                        all_goals
                            linarith
    -- Reverse direction: if p=2, q=3, r=7, then all expressions are integers
    .
        intro h
        rcases h with ⟨h1, h2, h3⟩
        subst p q r
        simp
        norm_num
        -- Verify that the three expressions evaluate to integers 1, 8, and 11
        exact ⟨⟨1, by norm_num⟩, ⟨8, by norm_num⟩, ⟨11, by norm_num⟩⟩
