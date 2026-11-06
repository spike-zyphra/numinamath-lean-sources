import Mathlib

-- we show all possible values of m^2 mod 5 for m not divisible by 5
lemma lemma_1 (m: ℕ) (h: ¬ 5 ∣ m): m ^ 2 % 5 = 1 ∨ m ^ 2 % 5 = 4 := by
    have r: m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
        omega
    have o: ¬ m % 5 = 0 := by
        by_contra! o
        apply Nat.dvd_of_mod_eq_zero at o
        tauto
    simp [o] at r
    rw [Nat.pow_mod]
    rcases r with r | r | r | r
    all_goals simp [r]


-- then we show that (m^2)^k mod 5 is either 1 or 4 for k a natural number and m not divisible by 5
lemma lemma_2 (m k: ℕ) (h: ¬ 5 ∣ m): (m ^ 2) ^ k % 5 = 1 ∨ (m ^ 2) ^ k % 5 = 4 := by
    have i:= lemma_1 m h
    rw [Nat.pow_mod]
    rcases i with i | i
    .
        simp [i]
    .
        simp [i]
        by_cases ok: Odd k
        .
            right
            apply Odd.exists_bit1 at ok
            obtain ⟨j, rfl⟩ := ok
            have s: 4 ^ (2 * j + 1) = 4 * 16 ^ j := by
                rw [Nat.pow_add]
                rw [Nat.pow_mul]
                ring
            rw [s]
            clear s
            rw [Nat.mul_mod]
            rw [Nat.pow_mod]
            simp
        .
            simp at ok
            rw [even_iff_exists_two_mul] at ok
            obtain ⟨j, rfl⟩ := ok
            left
            rw [Nat.pow_mul]
            simp
            rw [Nat.pow_mod]
            simp


-- we show a important lemma that if n is odd, then a + b divides a^n + b^n
lemma lemma_3 (a b n: ℕ) (o: Odd n) (ha: 0 < a): a + b ∣ a ^ n + b ^ n := by
    zify
    replace ha: (0: ℤ) < a := by
        simp
        tauto
    set x: ℤ := ↑a
    set y: ℤ := ↑b
    have ly: 0 ≤ y := by
        simp [y]
    clear_value x y

    -- prove by strong induction on n
    induction' n using Nat.strongRecOn with n ih
    by_cases l: n < 4
    .
        interval_cases n
        all_goals try {
            absurd o
            decide}
        -- n = 1
        .
            simp
        -- n = 3
        .
            rw [show x ^ 3 + y ^ 3 = (x + y) * (x ^ 2 - x * y + y ^ 2) by
                ring]
            simp

    .
        simp at l
        have eq: x ^ n + y ^ n = (x ^ (n - 2) + y ^ (n - 2)) * (x ^ 2 + y ^ 2) - (x ^ 2 * y ^ 2) * (x ^ (n - 4) + y ^ (n - 4)) := by
            ring_nf
            have s3: x ^ 2 * y ^ 2 * y ^ (n - 4) = x ^ 2 * y ^ (n - 2) := by
                rw [show n - 2 = n - 4 + 2 by omega]
                ring
            have s4: x ^ 2 * x ^ (n - 4) * y ^ 2 =  x ^ (n - 2) * y ^ 2 := by
                rw [show n - 2 = n - 4 + 2 by omega]
                ring
            simp [s3, s4]
            clear s3 s4
            ring_nf
            have s1: x ^ 2 * x ^ (n - 2) = x ^ n := by
                nth_rewrite 2 [show n = n - 2 + 2 by omega]
                ring
            have s2: y ^ 2 * y ^ (n - 2) = y ^ n := by
                nth_rewrite 2 [show n = n - 2 + 2 by omega]
                ring
            simp [s1, s2]
        rw [eq]
        clear eq
        apply dvd_sub
        .
            specialize ih (n - 2) (by omega)
            have i: Odd (n - 2) := by
                apply Nat.Odd.sub_even
                omega
                tauto
                decide
            simp [i] at ih
            have v: (x ^ (n - 2) + y ^ (n - 2)) ∣ (x ^ (n - 2) + y ^ (n - 2)) * (x ^ 2 + y ^ 2) := by
                simp
            apply dvd_trans ih v
        .
            have i: Odd (n - 4) := by
                apply Nat.Odd.sub_even
                omega
                tauto
                decide
            specialize ih (n - 4) (by omega)
            simp [i] at ih
            have v: (x ^ (n - 4) + y ^ (n - 4)) ∣ (x ^ 2 * y ^ 2 * (x ^ (n - 4) + y ^ (n - 4))) := by
                simp
            apply dvd_trans ih v


-- we write the case when p ≤ q as a lemma, then use symmetry to prove the other case in the main theorem
lemma lemma_4 (p q r n : ℕ) (l: p ≤ q) (hpqr : Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r)
    (hn : 0 < n) (h : p ^ n + q ^ n = r ^ 2) : n = 1 := by

    rcases hpqr with ⟨hp, hq, hr⟩
    by_contra! ln
    replace ln: 2 ≤ n := by
        omega
    clear hn
    by_cases lp: 2 < p

    -- case 2 < p, we show that r = 2 by parity
    .
        have op: Odd p := by
            apply Nat.Prime.odd_of_ne_two
            tauto
            omega
        have oq: Odd q := by
            apply Nat.Prime.odd_of_ne_two
            tauto
            omega
        have Or: Even r := by
            suffices Even (r ^ 2) by
                rw [Nat.even_pow'] at this
                tauto
                norm_num
            rw [← h]
            rw [Nat.even_add']
            have u: Odd (p ^ n) := by
                by_contra! f
                absurd op
                simp
                simp at f
                rw [Nat.even_pow'] at f
                tauto
                omega
            have v: Odd (q ^ n) := by
                by_contra! f
                absurd oq
                simp
                simp at f
                rw [Nat.even_pow'] at f
                tauto
                omega
            simp [u, v]
        rw [Nat.Prime.even_iff] at Or
        simp [Or] at h
        suffices 4 < p ^ n by omega
        suffices 4 < p ^ 2 ∧ p ^ 2 ≤ p ^ n by
            omega
        constructor
        .
            rw [show 4 = 2 ^ 2 by norm_num]
            apply Nat.pow_lt_pow_left
            omega
            norm_num
        .
            apply Nat.pow_le_pow_right
            omega
            tauto
        exact hr

    -- case p = 2
    .
        simp at lp
        have vp: p = 2 := by
            suffices p ≠ 0 ∧ p ≠ 1 by
                omega
            constructor
            .
                by_contra! f
                simp [f] at hp
                norm_num at hp
            .
                by_contra! f
                simp [f] at hp
                norm_num at hp
        simp [vp] at *
        clear hp lp vp

        -- then we check by parity of n
        by_cases g: Even n

        -- case n is even
        .
            rw [even_iff_exists_two_mul] at g
            obtain ⟨k, rfl⟩ := g
            replace ln: 1 ≤ k := by omega
            rw [show 2 ^ (2 * k) = 4 ^ k by rw [Nat.pow_mul]] at h
            rw [show q ^ (2 * k) = (q ^ 2) ^ k by rw [Nat.pow_mul]] at h

            -- then we show that 5 ∣ q ∨ 5 ∣ r by mod 5
            have d: 5 ∣ q ∨ 5 ∣ r := by
                by_contra! d
                rcases d with ⟨dq, dr⟩
                replace h: (4 ^ k + (q ^ 2) ^ k) % 5  = (↑r ^ 2) % 5 := by
                    rw [h]
                rw [Nat.add_mod] at h
                have u:= lemma_2 q k dq
                have v:= lemma_2 2 k (by omega)
                have w:= lemma_1 r dr
                rw [show 2 ^ 2 = 4 by norm_num] at v

                -- then we can check all cases mod 5 to see that the equation does not hold
                rcases u with u | u <;> rcases v with v | v <;> rcases w with w | w <;> simp [u, v, w] at h

            rcases d with d | d

            -- case 5 ∣ q, we mod 3 to see contradiction
            .
                rw [Nat.prime_dvd_prime_iff_eq] at d
                symm at d
                simp [d] at h
                replace h: (4 ^ k + 25 ^ k) % 3 = r ^ 2 % 3 := by
                    rw [h]
                rw [Nat.add_mod] at h
                rw [Nat.pow_mod] at h
                simp at h
                rw [Nat.add_mod] at h
                rw [Nat.pow_mod] at h
                simp at h
                rw [Nat.pow_mod] at h
                have u: r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by
                    omega
                rcases u with u | u | u
                .
                    simp [u] at h
                .
                    simp [u] at h
                .
                    simp [u] at h
                norm_num
                exact hq

            -- case 5 ∣ r
            .
                rw [Nat.prime_dvd_prime_iff_eq] at d
                symm at d
                simp [d] at h
                have i: k < 3 := by
                    by_contra! f
                    suffices 4 ^ 3 ≤ 4 ^ k by
                        omega
                    apply Nat.pow_le_pow_right
                    norm_num
                    tauto
                interval_cases k
                .
                    simp at h
                    replace h: q ^ 2 = 21 := by omega
                    have lq: q < 5 := by
                        clear *- h
                        nlinarith
                    have rq: 4 < q := by
                        clear *- h
                        nlinarith
                    omega
                .
                    simp at h
                    replace h: (q ^ 2) ^ 2 = 9 := by omega
                    suffices 4 ≤ q ^ 2 by nlinarith
                    rw [show 4 = 2 ^ 2 by norm_num]
                    apply Nat.pow_le_pow_left
                    tauto
                norm_num
                exact hr

        -- case n is odd
        .
            simp at g
            have d:= lemma_3 2 q n g (by omega)
            set x:= (2 ^ n + q ^ n) / (2 + q)
            have eq: 2 ^ n + q ^ n = (2 + q) * x := by
                simp [x]
                symm
                apply Nat.mul_div_cancel'
                tauto
            rw [eq] at h
            apply Nat.le_of_dvd at d
            have ux: 0 < x := by
                simp [x]
                exact d
            have ur: 0 < r := by
                suffices r ≠ 0 by omega
                by_contra! o
                simp [o] at hr
                norm_num at hr

            -- then we show that r ∣ 2 + q
            have f: r ∣ 2 + q := by
                by_contra! f
                rw [← Nat.Prime.coprime_iff_not_dvd] at f
                have f2: (r ^ 2).Coprime (2 + q) := by
                    apply Nat.Coprime.pow_left
                    tauto
                have v: r ^ 2 ∣ (2 + q) * x := by
                    rw [h]
                apply Nat.Coprime.dvd_of_dvd_mul_left f2 at v
                apply Nat.le_of_dvd at v
                rw [← h] at v
                have uy: 1 < 2 + q := by
                    omega
                clear *- ux uy v
                clear_value x
                nlinarith
                simp [x]
                exact d
                exact hr

            -- then we there is a size contradiction
            apply exists_eq_mul_right_of_dvd at f
            obtain ⟨y, fy⟩ := f
            have ly: 0 < y := by
                suffices y ≠ 0 by omega
                by_contra! o
                simp [o] at fy
            simp [fy] at h
            replace h: y * x = r := by
                rw [show r * y * x = r * (y * x) by ring] at h
                rw [show r ^ 2 = r * r by ring] at h
                clear *- h ur ux ly
                nlinarith
            have b: r ∣ y * x := by
                rw [h]
            rw [Nat.Prime.dvd_mul] at b
            rcases b with b | b
            .
                apply Nat.le_of_dvd at b
                rw [← h] at b
                replace b: x ≤ 1 := by
                    clear *- ly ux b
                    nlinarith
                have vx: x = 1 := by
                    omega
                simp [vx] at eq
                suffices 2 < 2 ^ n ∧ q < q ^ n by omega
                constructor
                .
                    rw [show 2 = 2 ^ 1 by norm_num]
                    apply Nat.pow_lt_pow_right
                    omega
                    omega
                .
                    nth_rewrite 1 [show q = q ^ 1 by norm_num]
                    apply Nat.pow_lt_pow_right
                    omega
                    omega
                omega
            .
                apply Nat.le_of_dvd at b
                rw [← h] at b
                replace b: y ≤ 1 := by
                    clear *- ly ux b
                    nlinarith
                have vy: y = 1 := by
                    omega
                simp [vy] at h fy
                simp [← fy, h] at eq
                ring_nf at eq
                have lq: 3 ≤ q := by
                    suffices q ≠ 2 by omega
                    by_contra! o
                    simp [o] at fy
                    simp [← fy] at hr
                    norm_num at hr
                suffices 4 + q * 4 + q ^ 2 < 2 ^ n + q ^ n by omega
                clear eq fy h vy b ly ur d
                clear_value x
                by_cases l: 4 ≤ n
                .
                    suffices 4 + q * 4 + q ^ 2 ≤ 4 * q ^ 2 ∧ 4 * q ^ 2 < 2 ^ n + q ^ n by linarith
                    constructor
                    .
                        nlinarith
                    .
                        have u: 0 < 2 ^ n := by
                            apply Nat.pow_pos
                            omega
                        suffices 4 * q ^ 2 ≤ q ^ n by omega
                        rw [show n = n - 2 + 2 by omega]
                        ring_nf
                        suffices 4 ≤ q ^ (n - 2) by nlinarith
                        rw [show 4 = 2 ^ 2 by norm_num]
                        suffices 2 ^ 2 ≤ 2 ^ (n - 2) ∧ 2 ^ (n - 2) ≤ q ^ (n - 2) by
                            omega
                        constructor
                        .
                            apply Nat.pow_le_pow_right
                            omega
                            omega
                        .
                            apply Nat.pow_le_pow_left
                            omega
                .
                    simp at l
                    have s: n = 2 ∨ n = 3 := by omega
                    rcases s with s | s
                    .
                        simp [s] at g
                        absurd g
                        decide
                    .
                        simp [s]
                        clear *- lq
                        nlinarith

                tauto

            exact hr
            suffices 0 < 2 ^ n by omega
            apply Nat.pow_pos
            norm_num


/- Let $p, q, r$ be primes and let $n$ be a positive integer such that $p^n + q^n = r^2$. Prove that $n = 1$.
Laurentiu Panaitopol -/

theorem number_theory_89758 (p q r n : ℕ) (hpqr : Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r)
    (hn : 0 < n) (h : p ^ n + q ^ n = r ^ 2) : n = 1 := by

    by_cases l: p ≤ q

    -- case p ≤ q, we can use lemma_2
    .
        exact lemma_4 p q r n l hpqr hn h

    -- case p > q, we can swap p and q
    .
        replace h: q ^ n + p ^ n = r ^ 2 := by
            rw [Nat.add_comm]
            tauto
        replace hpqr: Nat.Prime q ∧ Nat.Prime p ∧ Nat.Prime r := by
            tauto
        exact lemma_4 q p r n (by omega) hpqr hn h