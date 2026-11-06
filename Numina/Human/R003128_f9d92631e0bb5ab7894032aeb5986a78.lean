import Mathlib

/-Find all pairs of integer solutions (n, m) to
2 ^ (3 ^ n) = 3 ^ (2 ^ m) - 1-/

theorem number_theory_155796:
    {(n, m): ℕ × ℕ | 2 ^ (3 ^ n) = 3 ^ (2 ^ m) - 1} = {(0, 0), (1, 1)} := by

    ext ⟨n, m⟩
    constructor
    -- the forward direction
    .
        intro h
        simp at h
        simp
        set x:= 3 ^ n
        set y:= 2 ^ m
        have lx: 1 ≤ x := by
            simp [x]
            apply Nat.pow_pos
            norm_num
        have ly: 1 ≤ y := by
            simp [y]
            apply Nat.pow_pos
            norm_num
        by_cases l: x = 1
        -- case 1: x = 1
        .
            simp [l] at h
            replace h: 3 ^ y = 3 := by omega
            rw [Nat.pow_eq_self_iff] at h
            simp [x, y] at l h
            rw [show 1 = 3 ^ 0 by norm_num] at l
            rw [pow_right_inj₀] at l
            rw [show 1 = 2 ^ 0 by norm_num] at h
            rw [pow_right_inj₀] at h
            omega
            all_goals norm_num

        -- case 2: x ≠ 1
        .
            replace lx: 2 ≤ x := by omega
            clear l
            have d: 4 ∣ 2 ^ x := by
                rw [show x = x - 2 + 2 by omega]
                rw [Nat.pow_add]
                norm_num
            rw [h] at d

            -- then we show that y is evevn
            have ey: Even y := by
                by_contra! o
                simp at o
                have l: 1 ≤ 3 ^ y := by
                    apply Nat.pow_pos
                    norm_num
                replace d: 4 ∣ 3 ^ y + 3 := by
                    rw [show 3 ^ y + 3 = 3 ^ y - 1 + 4 by omega]
                    apply Nat.dvd_add
                    exact d
                    norm_num
                apply Nat.mod_eq_zero_of_dvd at d
                rw [Nat.add_mod] at d
                have u: 3 ^ y % 4 = 3 := by
                    apply Odd.exists_bit1 at o
                    obtain ⟨k, hk⟩ := o
                    simp [hk]
                    rw [show 3 ^ (2 * k + 1) = 3 ^ (2 * k) * 3 by omega]
                    rw [show 3 ^ (2 * k) = 9 ^ k by apply Nat.pow_mul]
                    rw [Nat.mul_mod]
                    have s: 9 ^ k % 4 = 1 := by
                        rw [Nat.pow_mod]
                        norm_num
                    rw [s]

                rw [u] at d
                norm_num at d

            rw [even_iff_exists_two_mul] at ey
            obtain ⟨k, hk⟩ := ey
            simp [hk] at h
            clear d
            rw [show 3 ^ (2 * k) = (3 ^ k) ^ 2 by rw [← Nat.pow_mul]; ring] at h
            have eq: (3 ^ k) ^ 2 - 1 = (3 ^ k - 1) * (3 ^ k + 1) := by
                set p:= 3 ^ k
                have lp: 1 ≤ p := by
                    simp [p]
                    apply Nat.pow_pos
                    norm_num
                clear_value p
                set q:= p - 1
                rw [show p = q + 1 by omega]
                ring_nf
                omega
            rw [eq] at h
            clear eq
            have lk: 1 ≤ 3 ^ k := by
                apply Nat.pow_pos
                norm_num
            set d:= 3 ^ k - 1
            rw [show 3 ^ k + 1 = d + 2 by simp [d]; omega] at h
            have d1: d ∣ 2 ^ x := by
                rw [h]
                simp
            rw [Nat.dvd_prime_pow] at d1
            obtain ⟨u, hu⟩ := d1
            have d2: d + 2 ∣ 2 ^ x := by
                rw [h]
                simp
            rw [Nat.dvd_prime_pow] at d2
            obtain ⟨v, hv⟩ := d2
            rcases hu with ⟨lu, hu⟩
            rcases hv with ⟨lv, hv⟩
            have i: u < v := by
                have t: 2 ^ u < 2 ^ v := by
                    omega
                rw [Nat.pow_lt_pow_iff_right] at t
                exact t
                norm_num
            rw [hu] at hv
            by_cases su: u = 0
            -- case 1: u = 0
            .
                simp [su] at hv
                simp [su] at i
                have j: 2 ∣ 3 := by
                    rw [hv]
                    rw [show v = v - 1 + 1 by omega]
                    rw [Nat.pow_add]
                    norm_num
                norm_num at j
            -- case 2: u ≠ 0
            .
                replace su: 1 ≤ u := by omega
                -- we show that u must be one
                have ou: u = 1 := by
                    by_contra! o
                    replace su: 2 ≤ u := by omega
                    clear o
                    have ov: 3 ≤ v := by omega
                    have t: 4 ∣ 2 ^ v := by
                        rw [show v = v - 2 + 2 by omega]
                        rw [Nat.pow_add]
                        norm_num
                    rw [← hv] at t
                    have c: 4 ∣ 2 := by
                        rw [show 2 = 2 ^ u + 2 - 2 ^ u by omega]
                        apply Nat.dvd_sub
                        .
                            omega
                        .
                            exact t
                        rw [show u = u - 2 + 2 by omega]
                        rw [Nat.pow_add]
                        norm_num
                    norm_num at c
                simp [ou, hv] at hu
                simp [hu] at h
                rw [show 8 = 2 ^ 3 by norm_num] at h
                rw [pow_right_inj₀] at h
                simp [d] at hu
                nth_rewrite 2 [show 3 = 3 ^ 1 by norm_num] at hu
                rw [pow_right_inj₀] at hu
                simp [hu] at hk
                simp [x, y] at hk h
                nth_rewrite 2 [show 3 = 3 ^ 1 by norm_num] at h
                rw [pow_right_inj₀] at h
                nth_rewrite 2 [show 2 = 2 ^ 1 by norm_num] at hk
                rw [pow_right_inj₀] at hk
                simp [h, hk]
                all_goals norm_num
            norm_num
            norm_num

    -- the backward direction
    .
        intro h
        simp at h
        rcases h with h | h
        .
            simp [h]
        .
            simp [h]
            
