import Mathlib

/-All positive integer solution pairs (x, y) of the equation
 x ^ 2 + y ^ 2 = 208 * (x - y) are -/

theorem algebra_296533: {(x, y): ℤ × ℤ | 0 < x ∧ 0 < y ∧
  x ^ 2 + y ^ 2 = 208 * (x - y)} = {(48, 32), (160, 32)} := by

    -- we first show that x ^ 2 % 4 = 1 for odd x
    have h_odd: ∀ x: ℤ, x % 2 = 1 → x ^ 2 % 4 = 1 := by
      intro x h
      rw [show x ^ 2 = x * x by ring]
      rw [Int.mul_emod]
      have s: x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
      have o: x % (2 * 2) % 2 = x % 2 := by
        apply Int.mod_mul_left_mod
      rw [show (2: ℤ) * 2 = 4 by rfl] at o
      rw [h] at o
      rcases s with s | s | s | s
      all_goals simp [s]
      all_goals simp [s] at o

    ext ⟨x, y⟩
    constructor
    -- the forward direction
    .
      intro h
      simp at h
      simp
      rcases h with ⟨hx, hy, h⟩

      -- we first show that x and y are even
      have p: 208 * (x - y) % 4 = 0 := by
            simp
            have r: 208 ∣ 208 * (x - y) := by
              simp
            have v: (4: ℤ) ∣ 208 := by norm_num
            apply dvd_trans v r
      rw [← h] at p
      rw [Int.add_emod] at p
      have ex: x % 2 = 0 := by
        by_contra! o
        replace o: x % 2 = 1 := by omega
        have q:= h_odd
        specialize h_odd x o
        have u: y % 2 = 0 ∨ y % 2 = 1 := by omega
        rcases u with u | u
        .
          have s: y ^ 2 % 4 = 0 := by
            rw [← Int.dvd_iff_emod_eq_zero] at u
            rw [← Int.dvd_iff_emod_eq_zero]
            rw [show (4: ℤ) = 2 ^ 2 by rfl]
            rw [Int.pow_dvd_pow_iff]
            exact u
            norm_num
          simp [s, h_odd] at p
        .
          specialize q y u
          simp [q, h_odd] at p
      have ey: y % 2 = 0 := by
        by_contra! o
        replace o: y % 2 = 1 := by omega
        have q:= h_odd
        specialize h_odd y o
        have s: x ^ 2 % 4 = 0 := by
          rw [← Int.dvd_iff_emod_eq_zero] at ex
          rw [← Int.dvd_iff_emod_eq_zero]
          rw [show (4: ℤ) = 2 ^ 2 by rfl]
          rw [Int.pow_dvd_pow_iff]
          exact ex
          norm_num
        simp [s, h_odd] at p

      simp at ex ey
      apply exists_eq_mul_right_of_dvd at ex
      obtain ⟨a, ha⟩ := ex
      apply exists_eq_mul_right_of_dvd at ey
      obtain ⟨b, hb⟩ := ey
      simp [ha, hb] at *
      clear p ha hb
      replace h: a ^ 2 + b ^ 2 = 104 * (a - b) := by nlinarith

      -- similarly, we show that a and b are even
      have p: 104 * (a - b) % 4 = 0 := by
            simp
            have r: 104 ∣ 104 * (a - b) := by
              simp
            have v: (4: ℤ) ∣ 104 := by norm_num
            apply dvd_trans v r
      rw [← h] at p
      rw [Int.add_emod] at p
      have ea: a % 2 = 0 := by
        by_contra! o
        replace o: a % 2 = 1 := by omega
        have q:= h_odd
        specialize h_odd a o
        have u: b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases u with u | u
        .
          have s: b ^ 2 % 4 = 0 := by
            rw [← Int.dvd_iff_emod_eq_zero] at u
            rw [← Int.dvd_iff_emod_eq_zero]
            rw [show (4: ℤ) = 2 ^ 2 by rfl]
            rw [Int.pow_dvd_pow_iff]
            exact u
            norm_num
          simp [s, h_odd] at p
        .
          specialize q b u
          simp [q, h_odd] at p
      have eb: b % 2 = 0 := by
        by_contra! o
        replace o: b % 2 = 1 := by omega
        have q:= h_odd
        specialize h_odd b o
        have s: a ^ 2 % 4 = 0 := by
          rw [← Int.dvd_iff_emod_eq_zero] at ea
          rw [← Int.dvd_iff_emod_eq_zero]
          rw [show (4: ℤ) = 2 ^ 2 by rfl]
          rw [Int.pow_dvd_pow_iff]
          exact ea
          norm_num
        simp [s, h_odd] at p

      simp at ea eb
      apply exists_eq_mul_right_of_dvd at ea
      obtain ⟨c, hc⟩ := ea
      apply exists_eq_mul_right_of_dvd at eb
      obtain ⟨d, hd⟩ := eb
      simp [hc, hd] at *
      clear p hc hd
      replace h: c ^ 2 + d ^ 2 = 52 * (c - d) := by nlinarith

      -- similarly, we show that c and d are even
      have p: 52 * (c - d) % 4 = 0 := by
            simp
            have r: 52 ∣ 52 * (c - d) := by
              simp
            have v: (4: ℤ) ∣ 52 := by norm_num
            apply dvd_trans v r
      rw [← h] at p
      rw [Int.add_emod] at p
      have ec: c % 2 = 0 := by
        by_contra! o
        replace o: c % 2 = 1 := by omega
        have q:= h_odd
        specialize h_odd c o
        have u: d % 2 = 0 ∨ d % 2 = 1 := by omega
        rcases u with u | u
        .
          have s: d ^ 2 % 4 = 0 := by
            rw [← Int.dvd_iff_emod_eq_zero] at u
            rw [← Int.dvd_iff_emod_eq_zero]
            rw [show (4: ℤ) = 2 ^ 2 by rfl]
            rw [Int.pow_dvd_pow_iff]
            exact u
            norm_num
          simp [s, h_odd] at p
        .
          specialize q d u
          simp [q, h_odd] at p
      have ed: d % 2 = 0 := by
        by_contra! o
        replace o: d % 2 = 1 := by omega
        have q:= h_odd
        specialize h_odd d o
        have s: c ^ 2 % 4 = 0 := by
          rw [← Int.dvd_iff_emod_eq_zero] at ec
          rw [← Int.dvd_iff_emod_eq_zero]
          rw [show (4: ℤ) = 2 ^ 2 by rfl]
          rw [Int.pow_dvd_pow_iff]
          exact ec
          norm_num
        simp [s, h_odd] at p

      simp at ec ed
      apply exists_eq_mul_right_of_dvd at ec
      obtain ⟨s, hs⟩ := ec
      apply exists_eq_mul_right_of_dvd at ed
      obtain ⟨t, ht⟩ := ed
      simp [hs, ht] at *
      clear p hs ht
      replace h: s ^ 2 + t ^ 2 = 26 * (s - t) := by nlinarith

      -- finally, we compute s and t
      have r: s = 6 ∧ t = 4 ∨ s = 20 ∧ t = 4 := by
        clear h_odd
        replace h: (s - 13) ^ 2 + (t + 13) ^ 2 = 2 * 13 ^ 2 := by nlinarith
        have ls: (s - 13) ^ 2 < 12 ^ 2 := by nlinarith
        apply abs_lt_of_sq_lt_sq at ls
        norm_num at ls
        set j:= |s - 13| with hj
        have oj: 0 ≤ j := by
          apply abs_nonneg
        have eq: (s - 13) ^ 2 = j ^ 2 := by
          simp [j]
        rw [eq] at h
        clear eq
        set k:= t + 13
        have lk: 14 ≤ k := by omega
        replace h: k ^ 2 = 338 - j ^ 2 := by omega

        -- then we check all value of j
        interval_cases j
        all_goals simp at h
        .
          have lk1: k < 19 := by nlinarith
          have lk2: k > 18 := by nlinarith
          omega
        .
          have lk1: k < 19 := by nlinarith
          have lk2: k > 18 := by nlinarith
          omega
        .
          have lk1: k < 19 := by nlinarith
          have lk2: k > 18 := by nlinarith
          omega
        .
          have lk1: k < 19 := by nlinarith
          have lk2: k > 18 := by nlinarith
          omega
        .
          have lk1: k < 18 := by nlinarith
          have lk2: k > 17 := by nlinarith
          omega
        .
          have lk1: k < 18 := by nlinarith
          have lk2: k > 17 := by nlinarith
          omega
        .
          have lk1: k < 18 := by nlinarith
          have lk2: k > 17 := by nlinarith
          omega
        .  -- this case gives the solution
          have rk: k = 17 := by nlinarith
          simp [k] at rk
          replace rk: t = 4 := by omega
          by_cases l: s ≤ 13
          .
            rw [show |s - 13| = - (s - 13) by apply abs_of_nonpos; linarith] at hj
            replace hj: s = 6 := by omega
            simp [hj, rk]
          .
            rw [show |s - 13| = s - 13 by apply abs_of_pos; linarith] at hj
            replace hj: s = 20 := by omega
            simp [hj, rk]
        .
          have lk1: k < 17 := by nlinarith
          have lk2: k > 16 := by nlinarith
          omega
        .
          have lk1: k < 17 := by nlinarith
          have lk2: k > 16 := by nlinarith
          omega
        .
          have lk1: k < 16 := by nlinarith
          have lk2: k > 15 := by nlinarith
          omega
        .
          have lk1: k < 15 := by nlinarith
          have lk2: k > 14 := by nlinarith
          omega

      -- plug the value of s and t back
      rcases r with r | r
      .
        simp [r]
      .
        simp [r]


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h
      .
        simp [h]
      .
        simp [h]
        