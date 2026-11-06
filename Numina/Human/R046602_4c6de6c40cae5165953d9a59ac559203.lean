import Mathlib

set_option maxHeartbeats 600000
/- Find all triplets $(a, b, c)$ of positive integers, such that
$a+bc, b+ac, c+ab$ are primes and all divide $(a^2+1)(b^2+1)(c^2+1)$. -/

theorem number_theory_43019: {(a, b, c): ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧
    Nat.Prime (a + b * c) ∧ Nat.Prime (b + a * c) ∧ Nat.Prime (c + a * b) ∧
    a + b * c ∣ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ∧ b + a * c ∣ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) ∧
    c + a * b ∣ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)} = {(1, 1, 1)} := by

    ext ⟨a, b, c⟩
    constructor
    -- the forward direction
    .
        intro h
        simp only [Set.mem_setOf_eq] at h
        simp
        by_contra! no -- for convenience, prove by contradiction
        rcases h with ⟨la, lb, lc, pa, pb, pc, da, db, dc⟩

        -- we first show that two of the three primes must be equal
        have h: a + b * c = b + a * c ∨ a + b * c = c + a * b ∨ b + a * c = c + a * b := by
            by_contra! h
            rcases h with ⟨ha, hb, hc⟩

            -- then their prod must divide (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)
            have d: (a + b * c) * (b + a * c) * (c + b * a)∣ (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by
                apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
                apply Nat.Coprime.mul
                rw [Nat.Prime.coprime_iff_not_dvd]
                by_contra! l
                rw [Nat.prime_dvd_prime_iff_eq] at l
                simp [l] at hb
                absurd hb
                ring
                exact pa
                rw [show b * a = a * b by ring]
                exact pc
                exact pa
                rw [Nat.Prime.coprime_iff_not_dvd]
                by_contra! l
                rw [Nat.prime_dvd_prime_iff_eq] at l
                simp [l] at hc
                absurd hc
                ring
                exact pb
                rw [show b * a = a * b by ring]
                exact pc
                exact pb
                apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
                rw [Nat.Prime.coprime_iff_not_dvd]
                by_contra! l
                rw [Nat.prime_dvd_prime_iff_eq] at l
                rw [l] at ha
                absurd ha
                ring
                exact pa
                exact pb
                exact pa
                exact da
                exact db
                rw [show b * a = a * b by ring]
                exact dc

            -- use d, we can derive a inequality, where we can find a contradiction
            apply Nat.le_of_dvd at d
            ring_nf at d
            zify at d
            replace d: (a: ℤ) * ↑b * ↑c + ↑a * ↑b * ↑c ^ 3 + ↑a * ↑b ^ 3 * ↑c + ↑a ^ 2 * ↑b ^ 2 + ↑a ^ 2 * ↑b ^ 2 * ↑c ^ 2 + ↑a ^ 2 * ↑c ^ 2 +
                ↑a ^ 3 * ↑b * ↑c + ↑b ^ 2 * ↑c ^ 2 -
                (1 + ↑a ^ 2 + ↑a ^ 2 * ↑b ^ 2 + ↑a ^ 2 * ↑b ^ 2 * ↑c ^ 2 +
                ↑a ^ 2 * ↑c ^ 2 + ↑b ^ 2 + ↑b ^ 2 * ↑c ^ 2 + ↑c ^ 2) ≤ 0 := by linarith
            have eq: (a: ℤ) * ↑b * ↑c + ↑a * ↑b * ↑c ^ 3 + ↑a * ↑b ^ 3 * ↑c + ↑a ^ 2 * ↑b ^ 2 + ↑a ^ 2 * ↑b ^ 2 * ↑c ^ 2 + ↑a ^ 2 * ↑c ^ 2 +
                ↑a ^ 3 * ↑b * ↑c + ↑b ^ 2 * ↑c ^ 2 -
                (1 + ↑a ^ 2 + ↑a ^ 2 * ↑b ^ 2 + ↑a ^ 2 * ↑b ^ 2 * ↑c ^ 2 + ↑a ^ 2 * ↑c ^ 2 +
                ↑b ^ 2 + ↑b ^ 2 * ↑c ^ 2 + ↑c ^ 2)
                = (a * b * c - 1) * (a ^ 2 + b ^ 2 + c ^ 2 + 1) := by ring
            rw [eq] at d
            clear eq
            have s1: 0 < (a: ℤ) * b * c - 1 := by
                simp
                by_contra! l
                norm_cast at l
                have ne: a * b * c ≠ 0 := by
                    by_contra! o
                    simp at o
                    rcases o with o | o
                    .
                        rcases o with o | o
                        .
                            simp [o] at la
                        .
                            simp [o] at lb
                    .
                        simp [o] at lc
                replace l: a * b * c = 1 := by omega
                have sc:= Nat.eq_one_of_mul_eq_one_left l
                simp [sc] at l
                rcases l with ⟨sa, sb⟩
                simp [sa, sb, sc] at no
            have s2: 0 < ↑a ^ 2 + ↑b ^ 2 + ↑c ^ 2 + 1 := by
                nlinarith
            absurd d
            simp
            nlinarith
            have o1: 0 < a ^ 2 + 1 := by nlinarith
            have o2: 0 < b ^ 2 + 1 := by nlinarith
            have o3: 0 < c ^ 2 + 1 := by nlinarith
            rw [Nat.mul_pos_iff_of_pos_left]
            exact o3
            rw [Nat.mul_pos_iff_of_pos_left]
            exact o2
            exact o1       

        -- then we can splits h to check them all
        rcases h with h | h | h
        -- case 1: a + b * c = b + a * c
        .
            zify at h
            replace h: ((a: ℤ) - b) * (c - 1) = 0 := by nlinarith
            simp at h
            rcases h with h | h
            -- case 1: a = b
            .   replace h: (a: ℤ) = b := by nlinarith
                simp at h
                symm at h
                simp [h] at *
                rw [show a + a * c = a * (1 + c) by ring] at pa
                clear pb h db dc
                rw [Nat.prime_mul_iff] at pa
                rcases pa with pa | pa
                .
                    rcases pa with ⟨s1,s2⟩
                    omega
                .
                    rcases pa with ⟨hc, ha⟩
                    simp [ha] at *
                    zify at da
                    rw [show ((c: ℤ) ^ 2 + 1) = (1 + c) ^ 2 - 2 * c by ring] at da
                    have o: 1 + (c: ℤ) ∣ 8 * c := by
                            rw [show 8 * (c: ℤ) =  4 * (1 + c) * (1 + c) -4 * ((1 + ↑c) ^ 2 - 2 * ↑c) by ring]
                            apply Int.dvd_sub
                            simp
                            exact da
                    norm_cast at o
                    apply Nat.Coprime.dvd_of_dvd_mul_right at o
                    rw [show 8 = 2 ^ 3 by norm_num] at o
                    apply Nat.Prime.dvd_of_dvd_pow at o
                    apply Nat.le_of_dvd at o
                    omega
                    norm_num
                    exact hc
                    apply Nat.Coprime.symm
                    rw [← Nat.coprime_self_sub_left]
                    rw [show 1 + c - c = 1 by omega]
                    apply Nat.coprime_one_left
                    omega
            -- case 2: c = 1
            .
                replace h: (c: ℤ) = 1 := by nlinarith
                simp at h
                simp [h] at *
                clear lc h pb db
                replace dc: 1 + a * b ∣ (a ^ 2 + 1) * (b ^ 2 + 1) := by
                    have pp: (1 + a * b).Coprime 2 := by
                        rw [Nat.Prime.coprime_iff_not_dvd]
                        by_contra! l
                        apply Nat.le_of_dvd at l
                        replace l: a * b ≤ 1 := by omega
                        have oa: a = 1 := by nlinarith
                        have ob: b = 1 := by nlinarith
                        simp [oa, ob] at no
                        norm_num
                        exact pc
                    apply Nat.Coprime.dvd_of_dvd_mul_right pp dc
                rw [Nat.Prime.dvd_mul] at dc
                by_cases l: a < b
                -- case a < b
                .
                    rcases dc with o | o
                    .
                        apply Nat.le_of_dvd at o
                        replace o: a * b ≤ a ^ 2 := by omega
                        replace o: b ≤ a := by nlinarith
                        omega
                        omega
                    .
                        have l: 1 + a * b ∣b * (b - a) := by
                            have eq: b * (b - a) = b ^ 2 + 1 - (1 + a * b) := by
                                zify [l]
                                rw [Int.natCast_sub]
                                rw [Int.natCast_add]
                                rw [Int.natCast_add]
                                rw [Int.natCast_mul]
                                rw [Int.natCast_pow]
                                ring
                                have o: a * b ≤ b ^ 2 := by nlinarith
                                nlinarith
                            rw [eq]
                            apply Nat.dvd_sub
                            nlinarith
                            exact o
                            simp
                        rw [Nat.Prime.dvd_mul] at l
                        rcases l with l | l
                        .
                            apply Nat.le_of_dvd at l
                            have s: b ≤ a * b := by nlinarith
                            nlinarith
                            omega
                        .
                            apply Nat.le_of_dvd at l
                            have s: b - a ≤ b := by omega
                            have s1: b ≤ a * b := by nlinarith
                            nlinarith
                            omega
                        exact pc
                 -- case b ≤ a
                .
                    simp at l
                    by_cases i: b = a
                    -- case b = a
                    .
                        simp [i] at pa
                        rw [show a + a = 2 * a by ring] at pa
                        rw [Nat.prime_mul_iff] at pa
                        rcases pa with pa | pa
                        .
                            rcases pa with ⟨s1,s2⟩
                            omega
                        .
                            norm_num at pa
                    -- case b < a
                    .
                        replace l: b < a := by omega
                        rcases dc with o | o
                        .
                            have l: 1 + a * b ∣a * (a - b) := by
                                have eq: a * (a - b) = a ^ 2 + 1 - (1 + a * b) := by
                                    zify [l]
                                    rw [Int.natCast_sub]
                                    rw [Int.natCast_add]
                                    rw [Int.natCast_add]
                                    rw [Int.natCast_mul]
                                    rw [Int.natCast_pow]
                                    ring
                                    have o: a * b ≤ a ^ 2 := by nlinarith
                                    nlinarith
                                rw [eq]
                                apply Nat.dvd_sub
                                nlinarith
                                exact o
                                simp
                            rw [Nat.Prime.dvd_mul] at l
                            rcases l with l | l
                            .
                                apply Nat.le_of_dvd at l
                                have s: a ≤ a * b := by nlinarith
                                nlinarith
                                omega
                            .
                                apply Nat.le_of_dvd at l
                                have s: a - b ≤ a := by omega
                                have s1: a ≤ a * b := by nlinarith
                                nlinarith
                                omega
                            exact pc
                        .
                            apply Nat.le_of_dvd at o
                            replace o: a * b ≤ b ^ 2 := by omega
                            replace o: a ≤ b := by nlinarith
                            omega
                            omega
                exact pc

        -- case 2: a + b * c = c + a * b
        .
            zify at h
            replace h: ((a: ℤ) - c) * (b - 1) = 0 := by nlinarith
            simp at h
            rcases h with h | h
            -- case 1: a = b
            .   replace h: (a: ℤ) = c := by nlinarith
                simp at h
                symm at h
                simp [h] at *
                rw [show a + b * a = a * (1 + b) by ring] at pa
                clear pb h db dc
                rw [Nat.prime_mul_iff] at pa
                rcases pa with pa | pa
                .
                    rcases pa with ⟨s1,s2⟩
                    omega
                .
                    rcases pa with ⟨hc, ha⟩
                    simp [ha] at *
                    zify at da
                    rw [show ((b: ℤ) ^ 2 + 1) = (1 + b) ^ 2 - 2 * b by ring] at da
                    have o: 1 + (b: ℤ) ∣ 8 * b := by
                            rw [show 8 * (b: ℤ) =  4 * (1 + b) * (1 + b) -4 * ((1 + ↑b) ^ 2 - 2 * ↑b) by ring]
                            apply Int.dvd_sub
                            simp
                            ring_nf
                            ring_nf at da
                            exact da
                    norm_cast at o
                    apply Nat.Coprime.dvd_of_dvd_mul_right at o
                    rw [show 8 = 2 ^ 3 by norm_num] at o
                    apply Nat.Prime.dvd_of_dvd_pow at o
                    apply Nat.le_of_dvd at o
                    omega
                    norm_num
                    exact hc
                    apply Nat.Coprime.symm
                    rw [← Nat.coprime_self_sub_left]
                    rw [show 1 + b - b = 1 by omega]
                    apply Nat.coprime_one_left
                    omega
            -- case 2: c = 1
            .
                replace h: (b: ℤ) = 1 := by nlinarith
                simp at h
                simp [h] at *
                replace db: 1 + a * c ∣ (a ^ 2 + 1) * (c ^ 2 + 1) := by
                    have pp: (1 + a * c).Coprime 2 := by
                        rw [Nat.Prime.coprime_iff_not_dvd]
                        by_contra! l
                        apply Nat.le_of_dvd at l
                        replace l: a * c ≤ 1 := by omega
                        have oa: a = 1 := by nlinarith
                        have ob: c = 1 := by nlinarith
                        simp [oa, ob] at no
                        norm_num
                        exact pb
                    rw [show (a ^ 2 + 1) * 2 * (c ^ 2 + 1) = (a ^ 2 + 1) * (c ^ 2 + 1) * 2 by ring] at db
                    apply Nat.Coprime.dvd_of_dvd_mul_right pp db
                rw [Nat.Prime.dvd_mul] at db
                by_cases l: a < c
                -- case a < c
                .
                    rcases db with o | o
                    .
                        apply Nat.le_of_dvd at o
                        replace o: a * c ≤ a ^ 2 := by omega
                        replace o: c ≤ a := by nlinarith
                        omega
                        omega
                    .
                        have l: 1 + a * c ∣c * (c - a) := by
                            have eq: c * (c - a) = c ^ 2 + 1 - (1 + a * c) := by
                                zify [l]
                                rw [Int.natCast_sub]
                                rw [Int.natCast_add]
                                rw [Int.natCast_add]
                                rw [Int.natCast_mul]
                                rw [Int.natCast_pow]
                                ring
                                have o: a * c ≤ c ^ 2 := by nlinarith
                                nlinarith
                            rw [eq]
                            apply Nat.dvd_sub
                            nlinarith
                            exact o
                            simp
                        rw [Nat.Prime.dvd_mul] at l
                        rcases l with l | l
                        .
                            apply Nat.le_of_dvd at l
                            have s: c ≤ a * c := by nlinarith
                            nlinarith
                            omega
                        .
                            apply Nat.le_of_dvd at l
                            have s: c - a ≤ c := by omega
                            have s1: c ≤ a * c := by nlinarith
                            nlinarith
                            omega
                        exact pb
                 -- case b ≤ a
                .
                    simp at l
                    by_cases i: c = a
                    -- case b = a
                    .
                        simp [i] at pa
                        rw [show a + a = 2 * a by ring] at pa
                        rw [Nat.prime_mul_iff] at pa
                        rcases pa with pa | pa
                        .
                            rcases pa with ⟨s1,s2⟩
                            omega
                        .
                            norm_num at pa
                    -- case b < a
                    .
                        replace l: c < a := by omega
                        rcases db with o | o
                        .
                            have l: 1 + a * c ∣a * (a - c) := by
                                have eq: a * (a - c) = a ^ 2 + 1 - (1 + a * c) := by
                                    zify [l]
                                    rw [Int.natCast_sub]
                                    rw [Int.natCast_add]
                                    rw [Int.natCast_add]
                                    rw [Int.natCast_mul]
                                    rw [Int.natCast_pow]
                                    ring
                                    have o: a * c ≤ a ^ 2 := by nlinarith
                                    nlinarith
                                rw [eq]
                                apply Nat.dvd_sub
                                nlinarith
                                exact o
                                simp
                            rw [Nat.Prime.dvd_mul] at l
                            rcases l with l | l
                            .
                                apply Nat.le_of_dvd at l
                                have s: a ≤ a * c := by nlinarith
                                nlinarith
                                omega
                            .
                                apply Nat.le_of_dvd at l
                                have s: a - c ≤ a := by omega
                                have s1: a ≤ a * c := by nlinarith
                                nlinarith
                                omega
                            exact pb
                        .
                            apply Nat.le_of_dvd at o
                            replace o: a * c ≤ c ^ 2 := by omega
                            replace o: a ≤ c := by nlinarith
                            omega
                            omega
                exact pb

         -- case 3: b + a * c = c + a * b
        .
            zify at h
            replace h: ((b: ℤ) - c) * (a - 1) = 0 := by nlinarith
            simp at h
            rcases h with h | h
            -- case 1: a = b
            .   replace h: (b: ℤ) = c := by nlinarith
                simp at h
                symm at h
                simp [h] at *
                rw [show b + a * b = b * (1 + a) by ring] at pb
                clear pa h da dc
                rw [Nat.prime_mul_iff] at pb
                rcases pb with pb | pb
                .
                    rcases pb with ⟨s1,s2⟩
                    omega
                .
                    rcases pb with ⟨hc, hb⟩
                    simp [hb] at *
                    zify at db
                    rw [show ((a: ℤ) ^ 2 + 1) = (1 + a) ^ 2 - 2 * a by ring] at db
                    have o: 1 + (a: ℤ) ∣ 8 * a := by
                            rw [show 8 * (a: ℤ) =  4 * (1 + a) * (1 + a) - 4 * ((1 + ↑a) ^ 2 - 2 * ↑a) by ring]
                            apply Int.dvd_sub
                            simp
                            ring_nf
                            ring_nf at db
                            exact db
                    norm_cast at o
                    apply Nat.Coprime.dvd_of_dvd_mul_right at o
                    rw [show 8 = 2 ^ 3 by norm_num] at o
                    apply Nat.Prime.dvd_of_dvd_pow at o
                    apply Nat.le_of_dvd at o
                    omega
                    norm_num
                    exact hc
                    apply Nat.Coprime.symm
                    rw [← Nat.coprime_self_sub_left]
                    rw [show 1 + a - a = 1 by omega]
                    apply Nat.coprime_one_left
                    omega
            -- case 2: c = 1
            .
                replace h: (a: ℤ) = 1 := by nlinarith
                simp at h
                simp [h] at *
                replace da: 1 + b * c ∣ (b ^ 2 + 1) * (c ^ 2 + 1) := by
                    have pp: (1 + b * c).Coprime 2 := by
                        rw [Nat.Prime.coprime_iff_not_dvd]
                        by_contra! l
                        apply Nat.le_of_dvd at l
                        replace l: b * c ≤ 1 := by omega
                        have ob: b = 1 := by nlinarith
                        have oa: c = 1 := by nlinarith
                        simp [oa, ob] at no
                        norm_num
                        exact pa
                    rw [show 2 * (b ^ 2 + 1) * (c ^ 2 + 1) = (b ^ 2 + 1) * (c ^ 2 + 1) * 2 by ring] at da
                    apply Nat.Coprime.dvd_of_dvd_mul_right pp da
                rw [Nat.Prime.dvd_mul] at da
                by_cases l: b < c
                -- case b < c
                .
                    rcases da with o | o
                    .
                        apply Nat.le_of_dvd at o
                        replace o: b * c ≤ b ^ 2 := by omega
                        replace o: c ≤ b := by nlinarith
                        omega
                        omega
                    .
                        have l: 1 + b * c ∣c * (c - b) := by
                            have eq: c * (c - b) = c ^ 2 + 1 - (1 + b * c) := by
                                zify [l]
                                rw [Int.natCast_sub]
                                rw [Int.natCast_add]
                                rw [Int.natCast_add]
                                rw [Int.natCast_mul]
                                rw [Int.natCast_pow]
                                ring
                                have o: b * c ≤ c ^ 2 := by nlinarith
                                nlinarith
                            rw [eq]
                            apply Nat.dvd_sub
                            nlinarith
                            exact o
                            simp
                        rw [Nat.Prime.dvd_mul] at l
                        rcases l with l | l
                        .
                            apply Nat.le_of_dvd at l
                            have s: c ≤ b * c := by nlinarith
                            nlinarith
                            omega
                        .
                            apply Nat.le_of_dvd at l
                            have s: c - b ≤ c := by omega
                            have s1: c ≤ b * c := by nlinarith
                            nlinarith
                            omega
                        exact pa

                 -- case c ≤ b
                .
                    simp at l
                    by_cases i: c = b
                    -- case c = b
                    .
                        simp [i] at pb
                        rw [show b + b = 2 * b by ring] at pb
                        rw [Nat.prime_mul_iff] at pb
                        rcases pb with pb | pb
                        .
                            rcases pb with ⟨s1,s2⟩
                            omega
                        .
                            norm_num at pb
                    -- case c < b
                    .
                        replace l: c < b := by omega
                        rcases da with o | o
                        .
                            have l: 1 + b * c ∣b * (b - c) := by
                                have eq: b * (b - c) = b ^ 2 + 1 - (1 + b * c) := by
                                    zify [l]
                                    rw [Int.natCast_sub]
                                    rw [Int.natCast_add]
                                    rw [Int.natCast_add]
                                    rw [Int.natCast_mul]
                                    rw [Int.natCast_pow]
                                    ring
                                    have o: b * c ≤ b ^ 2 := by nlinarith
                                    nlinarith
                                rw [eq]
                                apply Nat.dvd_sub
                                nlinarith
                                exact o
                                simp
                            rw [Nat.Prime.dvd_mul] at l
                            rcases l with l | l
                            .
                                apply Nat.le_of_dvd at l
                                have s: b ≤ b * c := by nlinarith
                                nlinarith
                                omega
                            .
                                apply Nat.le_of_dvd at l
                                have s: b - c ≤ b := by omega
                                have s1: b ≤ b * c := by nlinarith
                                nlinarith
                                omega
                            exact pa
                        .
                            apply Nat.le_of_dvd at o
                            replace o: b * c ≤ c ^ 2 := by omega
                            replace o: b ≤ c := by nlinarith
                            omega
                            omega
                exact pa
    
    -- the backward direction
    .
        intro h
        simp at h
        simp [h]
        norm_num