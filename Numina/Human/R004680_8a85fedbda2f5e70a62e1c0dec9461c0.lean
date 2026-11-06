import Mathlib

-- we first prove for the case when c ≤ b ≤ a, then use symmetry to prove for other cases
lemma lemma_1 (a b c: ℕ) (l2: c ≤ b) (l3: b ≤ a)
  (h1: a^2 + b^2 + c^2 = 2011) (h2: (a.gcd b).gcd c + (a.lcm b).lcm c = 388) :
  a = 43 ∧ b = 9 ∧ c = 9 := by

    -- we first take out the gcd
    set d:= (a.gcd b).gcd c with hd
    have da: d ∣ a := by
        have s1: d ∣ a.gcd b := by
            apply Nat.gcd_dvd_left
        have s2: a.gcd b ∣ a := by
            apply Nat.gcd_dvd_left
        apply dvd_trans s1 s2
    have db: d ∣ b := by
        have s1: d ∣ a.gcd b := by
            apply Nat.gcd_dvd_left
        have s2: a.gcd b ∣ b := by
            apply Nat.gcd_dvd_right
        apply dvd_trans s1 s2
    have dc: d ∣ c := by
        apply Nat.gcd_dvd_right
    apply exists_eq_mul_right_of_dvd at da
    obtain ⟨a1, da⟩ := da
    apply exists_eq_mul_right_of_dvd at db
    obtain ⟨b1, db⟩ := db
    apply exists_eq_mul_right_of_dvd at dc
    obtain ⟨c1, dc⟩ := dc

    simp [da, db, dc] at h1
    rw [show (d * a1) ^ 2 + (d * b1) ^ 2 + (d * c1) ^ 2 = d ^ 2 * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) by ring] at h1

    -- then d ^ 2 ∣ 2011
    have f1: d ^ 2 ∣ 2011 := by
        rw [← h1]
        simp

    -- then we show that d ∣ 388
    have f2: d ∣ 388 := by
        rw [← h2]
        apply Nat.dvd_add
        simp
        have o1: d ∣ c := by
            simp [d]
            apply Nat.gcd_dvd_right
        have o2: c ∣ (a.lcm b).lcm c := by
            apply Nat.dvd_lcm_right
        apply dvd_trans o1 o2

    -- combine f1 and f2, we show that d = 1
    have vd: d = 1 := by
        replace f1: d ∈ Nat.divisors 2011 := by
            simp
            have o1: d ∣ d ^ 2 := by
                rw [show d ^ 2 = d * d by ring]
                simp
            apply dvd_trans o1 f1
        rw [show Nat.divisors 2011 = {1, 2011} by native_decide] at f1
        simp at f1
        rcases f1 with t | t
        .
            simp [t]
        .
            simp [t] at f2
            norm_num at f2

    simp [vd] at *
    replace h2: (a.lcm b).lcm c = 387 := by omega
    rw [← da, ← db, ← dc] at h1
    clear da db dc f1 f2 vd
    have lc: c < 26 := by nlinarith
    have rc: c ∈ Nat.divisors 387 := by
        simp
        rw [← h2]
        apply Nat.dvd_lcm_right
    have rb: b ∈ Nat.divisors 387 := by
        simp
        rw [← h2]
        have s: b ∣ a.lcm b := by
            apply Nat.dvd_lcm_right
        have s2: a.lcm b ∣ (a.lcm b).lcm c := by
            apply Nat.dvd_lcm_left
        apply dvd_trans s s2
    have ra: a ∈ Nat.divisors 387 := by
        simp
        rw [← h2]
        have s: a ∣ a.lcm b := by
            apply Nat.dvd_lcm_left
        have s2: a.lcm b ∣ (a.lcm b).lcm c := by
            apply Nat.dvd_lcm_left
        apply dvd_trans s s2
    have pa: a < 45 := by nlinarith
    rw [show Nat.divisors 387 = {1, 3, 9, 43, 129, 387} by native_decide] at rc rb ra
    simp at rc
    rcases rc with t | t | t | t | t | t
    all_goals simp [t] at lc
    .
        simp [t] at *
        have la: 31 < a := by nlinarith
        rcases ra with v | v | v | v | v | v
        all_goals simp [v] at la pa
        .
            simp [v] at h1
            replace h1: b ^ 2 = 161 := by linarith
            have i: 12 < b := by nlinarith
            have j: b < 13 := by nlinarith
            omega
    .
        simp [t] at *
        have la: 31 < a := by nlinarith
        rcases ra with v | v | v | v | v | v
        all_goals simp [v] at la pa
        .
            simp [v] at h1
            replace h1: b ^ 2 = 153 := by linarith
            have i: 12 < b := by nlinarith
            have j: b < 13 := by nlinarith
            omega
    .
        simp [t] at *
        have la: 31 < a := by nlinarith
        rcases ra with v | v | v | v | v | v
        all_goals simp [v] at la pa
        .
            simp [v] at h1
            replace h1: b = 9 := by nlinarith
            simp [h1, v]


-- we need to show the technical lemma to tackle the symmetry
lemma lemma_2 (x y z: ℕ): (x.gcd y).gcd z = (y.gcd z).gcd x := by
    apply Nat.dvd_antisymm
    .
        rw [Nat.dvd_gcd_iff]
        constructor
        .
            rw [Nat.dvd_gcd_iff]
            constructor
            .
                have o1: (x.gcd y).gcd z ∣ x.gcd y := by
                    apply Nat.gcd_dvd_left
                have o2: x.gcd y ∣ y := by
                    apply Nat.gcd_dvd_right
                apply dvd_trans o1 o2
            .
                apply Nat.gcd_dvd_right
        .
            have o1: (x.gcd y).gcd z ∣ x.gcd y := by
                apply Nat.gcd_dvd_left
            have o2: x.gcd y ∣ x := by
                apply Nat.gcd_dvd_left
            apply dvd_trans o1 o2
    .
        rw [Nat.dvd_gcd_iff]
        constructor
        .
            rw [Nat.dvd_gcd_iff]
            constructor
            .
                apply Nat.gcd_dvd_right
            .
                have o1: (y.gcd z).gcd x ∣ y.gcd z := by
                    apply Nat.gcd_dvd_left
                have o2: y.gcd z ∣ y := by
                    apply Nat.gcd_dvd_left
                apply dvd_trans o1 o2
        .
            have o1: (y.gcd z).gcd x ∣ y.gcd z := by
                apply Nat.gcd_dvd_left
            have o2: y.gcd z ∣ z := by
                apply Nat.gcd_dvd_right
            apply dvd_trans o1 o2


-- similarly, we show the symmetry for lcm
lemma lemma_3 (x y z: ℕ): (x.lcm y).lcm z = (y.lcm z).lcm x := by
    apply Nat.dvd_antisymm
    .
        rw [Nat.lcm_dvd_iff]
        constructor
        .
            rw [Nat.lcm_dvd_iff]
            constructor
            .
                apply Nat.dvd_lcm_right
            .
                have o1: y ∣ y.lcm z := by
                    apply Nat.dvd_lcm_left
                have o2: y.lcm z ∣ (y.lcm z).lcm x := by
                    apply Nat.dvd_lcm_left
                apply dvd_trans o1 o2
        .
            have o1: z ∣ y.lcm z := by
                apply Nat.dvd_lcm_right
            have o2: y.lcm z ∣ (y.lcm z).lcm x := by
                apply Nat.dvd_lcm_left
            apply dvd_trans o1 o2
    .
        rw [Nat.lcm_dvd_iff]
        constructor
        .
            rw [Nat.lcm_dvd_iff]
            constructor
            .
                have o1: y ∣x.lcm y := by
                    apply Nat.dvd_lcm_right
                have o2: x.lcm y ∣ (x.lcm y).lcm z := by
                    apply Nat.dvd_lcm_left
                apply dvd_trans o1 o2
            .
                apply Nat.dvd_lcm_right
        .
            have o1: x ∣ x.lcm y := by
                apply Nat.dvd_lcm_left
            have o2: x.lcm y ∣ (x.lcm y).lcm z := by
                apply Nat.dvd_lcm_left
            apply dvd_trans o1 o2


/-Given three positive integers a, b, and c
whose squares sum to 2011, and the sum of their greatest common divisor and least common multiple is 388. Then the sum of the numbers
a, b and c-/

theorem number_theory_299352 {a b c: ℕ} (h1: a^2 + b^2 + c^2 = 2011) (h2: (a.gcd b).gcd c + (a.lcm b).lcm c = 388) :
    a + b + c = 61 := by

    have u: (c ≤ b ∧ b ≤ a) ∨ (c ≤ a ∧ a ≤ b) ∨ (b ≤ c ∧ c ≤ a) ∨ (b ≤ a ∧ a ≤ c)
        ∨ (a ≤ b ∧ b ≤ c) ∨ (a ≤ c ∧ c ≤ b):= by
        omega

    -- we use lemma_1 to check all orderings of a, b, c
    rcases u with u | u | u | u | u | u

    -- case 1: c ≤ b ≤ a
    .
        have i:= lemma_1 a b c (by omega) (by omega) h1 h2
        omega

    -- case 2: c ≤ a ≤ b
    .
        rw [show a ^ 2 + b ^ 2 + c ^ 2 = b ^ 2 + a ^ 2 + c ^ 2 by ring] at h1
        have s1: a.gcd b = b.gcd a := by
            apply Nat.gcd_comm
        have s2: a.lcm b = b.lcm a := by
            apply Nat.lcm_comm
        simp [s1, s2] at h1 h2
        have i:= lemma_1 b a c (by omega) (by omega) h1 h2
        omega

    -- case 3: b ≤ c ≤ a
    .
        rw [show a ^ 2 + b ^ 2 + c ^ 2 = a ^ 2 + c ^ 2 + b ^ 2 by ring] at h1
        have i:= lemma_1 a c b (by omega) (by omega) h1
        have s1: (a.gcd c).gcd b = (a.gcd b).gcd c := by
            rw [show a.gcd b = b.gcd a by apply Nat.gcd_comm]
            symm
            exact lemma_2 b a c
        rw [s1] at i
        have s2: (a.lcm c).lcm b = (a.lcm b).lcm c := by
            rw [show a.lcm b = b.lcm a by apply Nat.lcm_comm]
            symm
            exact lemma_3 b a c
        rw [s2] at i
        simp [h2] at i
        omega

    -- case 4: b ≤ a ≤ c
    .
        rw [show a ^ 2 + b ^ 2 + c ^ 2 = c ^ 2 + a ^ 2 + b ^ 2 by ring] at h1
        have s1: a.gcd b = b.gcd a := by
            apply Nat.gcd_comm
        have s2: a.lcm b = b.lcm a := by
            apply Nat.lcm_comm
        simp [s1, s2] at h1 h2
        have i:= lemma_1 c a b (by omega) (by omega) h1
        have s1: (c.gcd a).gcd b = (b.gcd a).gcd c := by
            rw [show c.gcd a = a.gcd c by apply Nat.gcd_comm]
            symm
            exact lemma_2 b a c
        rw [s1] at i
        have s2: (c.lcm a).lcm b = (b.lcm a).lcm c := by
            rw [show c.lcm a = a.lcm c by apply Nat.lcm_comm]
            symm
            exact lemma_3 b a c
        rw [s2] at i
        simp [h2] at i
        omega

    -- case 5: a ≤ b ≤ c
    .
        rw [show a ^ 2 + b ^ 2 + c ^ 2 = c ^ 2 + b ^ 2 + a ^ 2 by ring] at h1
        have s1: a.gcd b = b.gcd a := by
            apply Nat.gcd_comm
        have s2: a.lcm b = b.lcm a := by
            apply Nat.lcm_comm
        simp [s1, s2] at h1 h2
        have i:= lemma_1 c b a (by omega) (by omega) h1
        have s1: (c.gcd b).gcd a = (b.gcd a).gcd c := by
            exact lemma_2 c b a
        rw [s1] at i
        have s2: (c.lcm b).lcm a = (b.lcm a).lcm c := by
           exact lemma_3 c b a
        rw [s2] at i
        simp [h2] at i
        omega

    -- case 6: a ≤ c ≤ b
    .
        rw [show a ^ 2 + b ^ 2 + c ^ 2 = b ^ 2 + c ^ 2 + a ^ 2 by ring] at h1
        have s1: a.gcd b = b.gcd a := by
            apply Nat.gcd_comm
        have s2: a.lcm b = b.lcm a := by
            apply Nat.lcm_comm
        simp [s1, s2] at h1 h2
        have i:= lemma_1 b c a (by omega) (by omega) h1
        have s1: (b.gcd c).gcd a = (b.gcd a).gcd c := by
            rw [show b.gcd c = c.gcd b by apply Nat.gcd_comm]
            exact lemma_2 c b a
        rw [s1] at i
        have s2: (b.lcm c).lcm a = (b.lcm a).lcm c := by
            rw [show b.lcm c = c.lcm b by apply Nat.lcm_comm]
            exact lemma_3 c b a
        rw [s2] at i
        simp [h2] at i
        omega