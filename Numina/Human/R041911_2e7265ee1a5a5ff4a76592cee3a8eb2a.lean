import Mathlib

set_option maxHeartbeats 400000
/- Find all quadruples $(a, b, c, d)$ of positive integers satisfying $\gcd(a, b, c, d) = 1$ and
\[ a | b + c, ~ b | c + d, ~ c | d + a, ~ d | a + b. \]

[i]Vítězslav Kala (Czech Republic)[/i] -/

theorem number_theory_75043:
    {(a, b, c, d): ℕ × ℕ × ℕ × ℕ | 0 < b ∧ 0 < c ∧ 0 < d ∧ a = max a (max b (max c d))
    ∧ Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1 ∧
    a ∣ b + c ∧ b ∣ c + d ∧ c ∣ d + a ∧ d ∣ a + b}
    = {(1,1,1,1), (2,1,1,1), (3,2,1,1), (5,3,2,1), (5,4,1,3), (7,5,2,3), (3,1,2,1),
    (5,1,4,3), (5,2,3,1), (7,2,5,3), (7,3,4,5)} := by

    ext ⟨a,b,c,d⟩
    constructor
    -- the forward direction
    .
        intro h
        simp at h
        rcases h with ⟨hb, hc, hd, ha, g, da, db, dc, dd⟩
        apply exists_eq_mul_right_of_dvd at da
        obtain ⟨k, hk⟩ := da
        rcases ha with ⟨lb, lc, ld⟩

        -- we show that k ≤ 2
        have lk: k ≤ 2 := by
            nlinarith
        replace lk: k = 0 ∨ k = 2 ∨ k = 1 := by omega
        rcases lk with lk | lk | lk
        -- k = 0
        .
            simp [lk] at hk
            rcases hk with ⟨s, r⟩
            simp [s] at hb
        -- k = 2
        .
            simp [lk] at hk
            have sb: b = a := by omega
            have sc: c = a := by omega
            simp [sb, sc] at dc
            apply Nat.le_of_dvd at dc
            have sd: d = a := by omega
            simp [sb, sc, sd] at g
            simp
            left
            omega
            omega
        -- k = 1
        .
            simp [lk] at hk
            replace hk: a = b + c := by rw [hk]
            simp [hk] at *
            clear hk lb lc lk
            replace dc: c ∣ b + d := by
                rw [show b + d = d + (b + c) - c by omega]
                apply Nat.dvd_sub
                omega
                exact dc
                simp
            rw [show b + c + b = 2 * b + c by ring] at dd

            -- we check cases by the maximal value of b c d
            have r: (c ≤ b ∧ d ≤ b) ∨ (b < c ∧ d ≤ c) ∨ (b < d ∧ c < d) := by omega
            rcases r with r | r | r

            . -- c ≤ b ∧ d ≤ b
                apply exists_eq_mul_right_of_dvd at db
                obtain ⟨k, hk⟩ := db
                have lk: k ≤ 2 := by nlinarith
                replace lk: k = 0 ∨ k = 1 ∨ k = 2 := by omega
                rcases lk with lk | lk | lk
                -- k = 0
                .
                    simp [lk] at hk
                    rcases hk with ⟨s, r⟩
                    simp [s] at hc
                -- k = 1
                .
                    rcases r with ⟨s, r⟩
                    simp [lk] at hk
                    replace hk: b = c + d := by rw [hk]
                    simp [hk] at *
                    replace dc: c ∣ 2 * d := by
                        rw [show 2 * d = c + d + d - c by omega]
                        apply Nat.dvd_sub
                        omega
                        exact dc
                        simp
                    replace dd: d ∣ 3 * c := by
                        rw [show 3 * c = 2 * (c + d) + c - 2 * d by omega]
                        apply Nat.dvd_sub
                        omega
                        exact dd
                        simp
                    rw [← Nat.coprime_iff_gcd_eq_one] at g
                    replace dc: c ∣ 2 := by
                        apply Nat.Coprime.dvd_of_dvd_mul_right g dc
                    replace dd: d ∣ 3 := by
                        apply Nat.Coprime.symm at g
                        apply Nat.Coprime.dvd_of_dvd_mul_right g dd
                    clear lk ld s r hk hb
                    have pc:= dc
                    apply Nat.le_of_dvd at dc
                    have pd:= dd
                    apply Nat.le_of_dvd at dd
                    have vd: d = 1 ∨ d = 3:= by
                        have o: d ≠ 2 := by
                            by_contra! o
                            simp [o] at pd
                            norm_num at pd
                        omega
                    have vc: c = 1 ∨ c = 2 := by omega
                    rcases vd with vd | vd
                    -- d = 1
                    .
                        rcases vc with vc | vc
                        -- c = 1
                        .
                            have o: c + d + c = 3 ∧ c = 1 ∧ d = 1 := by
                                omega
                            simp [o]
                        -- c = 2
                        .
                            have o: c + d + c = 5 ∧ c = 2 ∧ d = 1 := by
                                omega
                            simp [o]
                    -- d = 3
                    .
                        rcases vc with vc | vc
                        -- c = 1
                        .
                            have o: c + d + c = 5 ∧ c = 1 ∧ d = 3 := by
                                omega
                            simp [o]
                        -- c = 2
                        .
                            have o: c + d + c = 7 ∧ c = 2 ∧ d = 3 := by
                                omega
                            simp [o]
                    norm_num
                    norm_num
                .-- k = 2
                    simp [lk] at hk
                    have sb: c = b := by omega
                    have sc: d = b := by omega
                    simp [sb, sc] at g
                    have o: b + c = 2 ∧ b = 1 ∧ c = 1 ∧ d = 1:= by
                        omega
                    simp [o]

            . -- b < c ∧ d ≤ c
                apply exists_eq_mul_right_of_dvd at dc
                obtain ⟨k, hk⟩ := dc
                have lk: k < 2 := by nlinarith
                have vk: k = 1 := by
                    have o: k ≠ 0 := by
                        by_contra! o
                        simp [o] at hk
                        rcases hk with ⟨s, r⟩
                        simp [s] at hb
                    omega
                simp [vk] at hk
                replace hk: c = b + d := by rw [hk]
                simp [hk] at *
                replace dd: d ∣ 3 * b := by
                    rw [show 3 * b = 2 * b + (b + d) - d by omega]
                    apply Nat.dvd_sub
                    omega
                    exact dd
                    simp
                replace db: b ∣ 2 * d := by
                    rw [show 2 * d = b + d + d - b by omega]
                    apply Nat.dvd_sub
                    omega
                    exact db
                    simp
                rw [show d.gcd b = b.gcd d by rw [Nat.gcd_comm]] at g
                simp at g
                rw [← Nat.coprime_iff_gcd_eq_one] at g
                replace db: b ∣ 2 := by
                    apply Nat.Coprime.dvd_of_dvd_mul_right g db
                replace dd: d ∣ 3 := by
                    apply Nat.Coprime.symm at g
                    apply Nat.Coprime.dvd_of_dvd_mul_right g dd
                have pb:= db
                apply Nat.le_of_dvd at db
                have pd:= dd
                apply Nat.le_of_dvd at dd
                have vb: b = 1 ∨ b = 2 := by omega
                have vd: d = 1 ∨ d = 3 := by
                    have o: d ≠ 2 := by
                        by_contra! o
                        simp [o] at pd
                        norm_num at pd
                    omega
                rcases vb with vb | vb
                -- b = 1
                .
                    rcases vd with vd | vd
                    -- d = 1
                    .
                        have o: b + (b + d) = 3 ∧ b = 1 ∧ d = 1 := by
                            omega
                        simp [o]
                    -- d = 3
                    .
                        have o: b + (b + d) = 5 ∧ b = 1 ∧ d = 3 := by
                            omega
                        simp [o]
                -- b = 2
                .
                    rcases vd with vd | vd
                    -- d = 1
                    .
                        have o: b + (b + d) = 5 ∧ b = 2 ∧ d = 1 := by
                            omega
                        simp [o]
                    -- d = 3
                    .
                        have o: b + (b + d) = 7 ∧ b = 2 ∧ d = 3 := by
                            omega
                        simp [o]
                norm_num
                norm_num

            . -- b < d ∧ c < d
                apply exists_eq_mul_right_of_dvd at dd
                obtain ⟨k, hk⟩ := dd
                have lk: k < 3 := by nlinarith
                have lk2: 1 < k := by nlinarith
                have vk: k = 2 := by omega
                simp [vk] at hk
                have u: 2 ∣ c := by
                    rw [show c = (2 * b + c) - 2 * b by omega]
                    apply Nat.dvd_sub
                    omega
                    rw [hk]
                    simp
                    simp
                apply exists_eq_mul_right_of_dvd at u
                obtain ⟨x, hx⟩ := u
                simp [hx] at hk
                replace hk: d = b + x := by omega
                simp [hk] at *
                simp [hx] at *

                -- then we show that x and b are coprime
                have o: x.gcd b = 1 := by
                    set q:= x.gcd b
                    have q1: q ∣ x := by
                        simp [q]
                        apply Nat.gcd_dvd_left
                    have q2: q ∣ b := by
                        simp [q]
                        apply Nat.gcd_dvd_right
                    have q3: q ∣ (2 * x).gcd b := by
                        simp [q]
                        apply Nat.gcd_dvd_gcd_of_dvd_left
                        simp
                    have q4: q ∣ (2 * x).gcd (b + x) := by
                        rw [Nat.dvd_gcd_iff]
                        constructor
                        .
                            have o: x ∣ 2 * x := by simp
                            apply dvd_trans q1 o
                        .
                            apply Nat.dvd_add
                            exact q2
                            exact q1
                    have s: q ∣ ((2 * x).gcd b).gcd ((2 * x).gcd (b + x)) := by
                         rw [Nat.dvd_gcd_iff]
                         simp [q3,q4]
                    rw [g] at s
                    simp at s
                    exact s
                rw [← Nat.coprime_iff_gcd_eq_one] at o
                have t:= dc
                replace dc: x ∣ b + (b + x) := by
                    have o: x ∣ 2 * x := by simp
                    apply dvd_trans o dc
                replace dc: x ∣ 2 * b := by
                    rw [show 2 * b = b + (b + x) - x by omega]
                    apply Nat.dvd_sub
                    omega
                    exact dc
                    simp
                replace dc: x ∣ 2 := by
                    apply Nat.Coprime.dvd_of_dvd_mul_right o dc
                replace db: b ∣ 3 := by
                    rw [show 2 * x + (b + x) = 3 * x + b by omega] at db
                    have p: b ∣ 3 * x := by
                        rw [show 3 * x = 3 * x + b - b by omega]
                        apply Nat.dvd_sub
                        omega
                        exact db
                        simp
                    apply Nat.Coprime.symm at o
                    apply Nat.Coprime.dvd_of_dvd_mul_right o p
                have px:= dc
                apply Nat.le_of_dvd at dc
                have pb:= db
                apply Nat.le_of_dvd at db
                have vx: x = 1 ∨ x = 2 := by
                    omega
                have vb: b = 1 ∨ b = 3 := by
                    have y: b ≠ 2 := by
                        by_contra! y
                        simp [y] at pb
                        norm_num at pb
                    omega
                rcases vx with vx | vx
                -- x = 1
                .
                    rcases vb with vb | vb
                    -- b = 1
                    .
                        simp [vx, vb] at r
                    -- b = 3
                    .
                       simp [vx, vb] at t
                       norm_num at t
                -- x = 2
                .
                    rcases vb with vb | vb
                    -- b = 1
                    .
                        simp [vx,vb] at r
                    -- b = 3
                    .
                        have o: b + 2 * x = 7 ∧ b = 3 ∧ x = 2 := by
                            omega
                        simp [o]
                norm_num
                norm_num


    -- the backward direction
    .
        intro h
        simp at h
        rcases h with h | h | h | h | h | h | h | h | h | h | h
        all_goals simp [h]
        all_goals omega