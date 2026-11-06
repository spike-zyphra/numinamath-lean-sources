import Mathlib

/- Find all triples $(a, b, c)$ of nonnegative integers that satisfy

$$
a!+5^{b}=7^{c}
$$ -/
theorem number_theory_606185 (a b c : ℕ) :
    Nat.factorial a + 5^b = 7^c ↔ (a = 3 ∧ b = 0 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 1) ∨ (a = 4 ∧ b = 2 ∧ c = 2) := by

    constructor
    ·
      intro h_eq
      -- we cannot have c = 0 as a! + 5^b ≥ 2 > 1 = 7^0
      have c_nz : c ≠ 0 := by
        by_contra! h
        rw [h, pow_zero] at h_eq
        have : a.factorial ≥ 1 := by
          refine Nat.one_le_iff_ne_zero.mpr ?_
          exact Nat.factorial_ne_zero a
        have : 5 ^ b ≥ 1 := by exact Nat.one_le_pow' b 4
        linarith

      have c_pos : c > 0 := by exact Nat.zero_lt_of_ne_zero c_nz

      by_cases hb : b = 0
      · -- assume first that b = 0
        rw [hb, pow_zero] at h_eq -- so we are solving a! + 1 = 7 ^ c
        -- we deduce 7^c ∣ a!+1
        have : 7^c ∣ a.factorial + 1 := by exact dvd_of_eq (id (Eq.symm h_eq))
        have lhs_dvd_by_7 : 7 ∣ a.factorial + 1 := by exact Nat.dvd_of_pow_dvd c_pos this
        by_cases ha : a ≥ 7
        · -- if a ≥ 7, then 7 ∣ a!
          have : 7 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
          -- so 7 does not divides a! + 1
          have : ¬ 7 ∣ a.factorial + 1 := by
            by_contra! h
            have : 7 ∣ 1 := by exact (Nat.dvd_add_iff_right this).mpr h
            norm_num at this
          contradiction
        -- checking a < 7 by hand, the solution is (3, 0, 1)
        have : 7 ^ c ≥ 7 := by exact Nat.le_self_pow c_nz 7
        interval_cases a
        all_goals simp [Nat.factorial] at h_eq lhs_dvd_by_7;
        repeat linarith -- a = 0, 1, 2 is impossible as a! + 1 < 7 ≤ 7^c
        · left; simp [hb] -- a = 3, the solution is (3, 0, 1)
          by_contra! h
          have : c > 1 := by exact Nat.lt_of_le_of_ne c_pos (id (Ne.symm h))
          have : 7 ^ c > 7 ^ 1 := Nat.pow_lt_pow_of_lt (by norm_num) this
          linarith
        all_goals norm_num at lhs_dvd_by_7 -- a = 4, 5, we have 7 not divides a! + 1
        -- for a = 6, we canot have 7^c = a! + 1 = 721
        have : 7 ^ 3 < 721 := by norm_num
        have : c > 3 := by
          by_contra! h
          have : 7 ^ c ≤ 7 ^ 3 := Nat.pow_le_pow_of_le (by norm_num) h
          linarith
        have : 7 ^ 4 > 721 := by norm_num
        have : c < 4 := by
          by_contra! h
          have : 7 ^ 4 ≤ 7 ^ c := Nat.pow_le_pow_of_le (by norm_num) h
          linarith
        linarith

      -- we now assume that b > 0
      have b_pos : b > 0 := by exact Nat.zero_lt_of_ne_zero hb

      by_cases ha : a ≥ 5
      · -- if a ≥ 5, we have 5 ∣ a!
        have : 5 ∣ a.factorial := Nat.dvd_factorial (by norm_num) ha
        -- clearly 5 ∣ 5^b
        have : 5 ∣ 5 ^ b := by exact dvd_pow_self 5 hb
        -- so 5 ∣ 7 ^ c
        have : 5 ∣ 7 ^ c := by rw [← h_eq]; apply Nat.dvd_add; assumption; assumption
        -- but 5 does not divides 7 ^ C for any C
        have (C) : ¬ 5 ∣ 7 ^ C := by
          induction' C with C ih
          · norm_num
          · rw [pow_add, pow_one]
            by_contra! h
            have : 5 ∣ 7 ^ C ∨ 5 ∣ 7 := by refine (Nat.Prime.dvd_mul (by norm_num)).mp h
            norm_num at this
            contradiction
        have := this c
        contradiction
      -- so we have a ≤ 4
      interval_cases a
      repeat  -- if a = 0 or a = 1, we are solving 5 ^ b + 1 = 7 ^ c, but LHS is even while RHS is odd
        simp [Nat.factorial] at h_eq
        have : Even (1 + 5 ^ b) := by
          refine Nat.even_add'.mpr ?_
          simp
          apply Odd.pow
          exact Nat.odd_iff.mpr rfl
        have : Odd (7 ^ c) := by
          apply Odd.pow
          exact Nat.odd_iff.mpr rfl
        have : ¬ Even (7 ^ c) := by exact Nat.not_even_iff_odd.mpr this
        rw [← h_eq] at this
        contradiction
      · -- suppose a = 2, we are solving 5 ^ b + 2 = 7 ^ c
        simp [Nat.factorial] at h_eq
        by_cases hb' : b = 1
        · -- if b = 1, we have the solution (2, 1, 1)
          simp [hb'] at h_eq ⊢
          by_contra! h
          have : c > 1 := by exact Nat.lt_of_le_of_ne c_pos (id (Ne.symm h))
          have : 7 ^ c > 7 ^ 1 := Nat.pow_lt_pow_of_lt (by norm_num) this
          linarith
        -- now assume b ≥ 2, we have 5 ^ b + 2 = 7 ^ c
        have : b > 1 := by exact Nat.lt_of_le_of_ne b_pos fun a ↦ hb' (id (Eq.symm a))
        have : b ≥ 2 := this
        have : 5 ^ 2 ∣ 5 ^ b := by exact Nat.pow_dvd_pow_iff_le_right'.mpr this
        norm_num at this
        -- so 7 ^ c ≡ 2 mod 25
        have rhs_mod_25_eq_2 : 7 ^ c ≡ 2 [MOD 25] := by
          rw [← h_eq]
          refine Nat.ModEq.symm (Nat.modEq_of_dvd ?_)
          rw [Nat.cast_add]
          simp
          norm_cast
        -- by observing 7 ^ 4 ≡ 1 mod 25, we deduce 7 ^ c ≡ 7 ^ (c % 4) mod 25
        have h_7_c : 7 ^ c ≡ 7 ^ (c % 4) [MOD 25] := by
          have : c = (c / 4) * 4 + (c % 4) := by exact Eq.symm (Nat.div_add_mod' c 4)
          nth_rw 1 [this]
          rw [pow_add]
          nth_rw 2 [mul_comm]
          have : 7 ^ (4 * (c / 4)) ≡ 1 [MOD 25] := by
            generalize c / 4 = k
            induction' k with k ih
            · norm_num
              rfl
            · rw [mul_add, pow_add]
              norm_num
              have : 2401 ≡ 1 [MOD 25] := by rfl
              rw [show 1 = 1 * 1 by ring]
              exact Nat.ModEq.mul ih this
          nth_rw 2 [show 7 ^ (c % 4) = 1 * 7 ^ (c % 4) by ring]
          apply Nat.ModEq.mul_right
          assumption
        -- so 7 ^ c mod 25 can only be 7, 49 ≡ 24, 343 ≡ 18, or 1
        have : 7 ^ c ≡ 7 [MOD 25] ∨ 7 ^ c ≡ 49 [MOD 25] ∨ 7 ^ c ≡ 343 [MOD 25] ∨ 7 ^ c ≡ 1 [MOD 25] := by
          have _ : c % 4 < 4 := Nat.mod_lt c (by norm_num)
          interval_cases c % 4
          all_goals norm_num at h_7_c;
          repeat simp [h_7_c]
        -- so this case has no more solutions
        rcases this with h | h | h | h
        repeat
          have := Nat.ModEq.trans (rhs_mod_25_eq_2.symm) h
          unfold Nat.ModEq at this
          norm_num at this

      · -- suppose a = 3, we are solving 5 ^ b + 6 = 7 ^ c
        simp [Nat.factorial] at h_eq
        -- we have 5^b + 6 ≡ 1 mod 5
        have : 6 + 5 ^ b ≡ 1 [MOD 5] := by
          refine Nat.ModEq.symm (Nat.modEq_of_dvd ?_)
          rw [Nat.cast_add]
          simp
          rw [show 6 + 5 ^ b - 1 = 5 ^ b + (5 : ℤ) by ring]
          simp
          exact dvd_pow_self 5 hb
        -- this implies 7 ^ c ≡ 1 mod 25
        have : 7 ^ c ≡ 1 [MOD 5] := by
          trans 6 + 5 ^ b
          exact congrFun (congrArg HMod.hMod (id (Eq.symm h_eq))) 5
          exact this
        -- by observing 7 ^ 4 ≡ 1 mod 5, we deduce 7 ^ c ≡ 7 ^ (c % 4) mod 5
        have h_7_c : 7 ^ c ≡ 7 ^ (c % 4) [MOD 5] := by
          have : c = (c / 4) * 4 + (c % 4) := by exact Eq.symm (Nat.div_add_mod' c 4)
          nth_rw 1 [this]
          rw [pow_add]
          nth_rw 2 [mul_comm]
          have : 7 ^ (4 * (c / 4)) ≡ 1 [MOD 5] := by
            generalize c / 4 = k
            induction' k with k ih
            · norm_num
              rfl
            · rw [mul_add, pow_add]
              norm_num
              have : 2401 ≡ 1 [MOD 25] := by rfl
              rw [show 1 = 1 * 1 by ring]
              exact Nat.ModEq.mul ih this
          nth_rw 2 [show 7 ^ (c % 4) = 1 * 7 ^ (c % 4) by ring]
          apply Nat.ModEq.mul_right
          assumption
        -- enumerating c % 4, we deduce 4 ∣ c
        have c_dvd_by_4 : 4 ∣ c := by
          suffices h : c % 4 = 0 by exact Nat.dvd_of_mod_eq_zero h
          have _ : c % 4 < 4 := Nat.mod_lt c (by norm_num)
          interval_cases c % 4
          · simp
          repeat
            have h_con := Nat.ModEq.trans (this.symm) h_7_c
            unfold Nat.ModEq at h_con
            norm_num at h_con
        -- viewing the equation modulo 4
        have h_eq_mod_4 : 7 ^ c ≡ 3 [MOD 4] := by
          rw [← h_eq]
          calc
            6 + 5 ^ b ≡ 2 + 5 ^ b [MOD 4] := by exact Nat.ModEq.add_right (5 ^ b) rfl
            _ ≡ 2 + 1 ^ b [MOD 4] := by apply Nat.ModEq.add_left 2; exact Nat.ModEq.pow b rfl
            _ ≡ 2 + 1 [MOD 4] := by congr; ring
            _ ≡ 3 [MOD 4] := by congr
        -- but as 4 ∣ c, we know that 7 ^ c is a square
        obtain ⟨k, hk⟩ := c_dvd_by_4
        have h_sq_7_c : 7 ^ c = (7 ^ (2 * k)) ^ 2 := by rw [hk]; ring
        generalize 7 ^ (2 * k) = K at h_sq_7_c
        rw [h_sq_7_c] at h_eq_mod_4
        -- but the only residues that a square can have when divided by 4 are 0, 1.
        have sq_mod_4 (n : ℕ) : n ^ 2 ≡ 0 [MOD 4] ∨ n ^ 2 ≡ 1 [MOD 4] := by
          by_cases h_even : Even n
          · left
            obtain ⟨t, ht⟩ := h_even
            rw [ht, ← two_mul, mul_pow]
            norm_num
            suffices h : 4 ∣ 4 * t ^ 2 by exact Nat.modEq_zero_iff_dvd.mpr h
            exact Nat.dvd_mul_right 4 (t ^ 2)
          · right
            have : Odd n := by exact Nat.not_even_iff_odd.mp h_even
            obtain ⟨t, ht⟩ := this
            rw [ht, add_pow_two, mul_pow, ← mul_assoc]
            simp
            symm
            apply Nat.modEq_iff_dvd.mpr
            simp
            rw [← mul_add]
            exact Int.dvd_mul_right 4 (↑t ^ 2 + ↑t)
        rcases sq_mod_4 K with h | h
        repeat
          have := Nat.ModEq.trans h_eq_mod_4.symm h; unfold Nat.ModEq at this; norm_num at this
      · -- suppose a = 4, now we are solving the equation 5 6 b + 24 = 7 ^ c
        simp [Nat.factorial] at h_eq
        -- we have 5^b ≡ 7^c - 24 ≡ 1 mod 3
        have h_5_b_mod_3 : 5 ^ b ≡ 1 [ZMOD 3] := by
          have : (5 ^ b : ℤ) = 7 ^ c - 24 := by
            linarith
          rw [this]
          have : 7 ^ c ≡ 1 [ZMOD 3] := by
            trans 1 ^ c
            exact Int.ModEq.pow c rfl
            simp
          have : 24 ≡ 0 [ZMOD 3] := by rfl
          trans 1 - 0
          apply Int.ModEq.sub (by assumption) (by assumption)
          rfl
        -- since 5 ≡ 2 mod 3, we have 2 ∣ b
        have h_5_b' : 5 ^ b ≡ (-1) ^ b [ZMOD 3] := by
          exact Int.ModEq.pow b rfl
        have : Even b := by
          by_contra! h
          have : Odd b := by exact Nat.not_even_iff_odd.mp h
          have : (-1) ^ b = -1 := by exact Odd.neg_one_pow this
          rw [this] at h_5_b'
          have := Int.ModEq.trans h_5_b_mod_3.symm h_5_b'
          unfold Int.ModEq at this
          norm_num at this
        -- let b = 2 * m
        obtain ⟨m, hm⟩ := this

        -- we also have 7^c = 5^b + 24 ≡ 4 mod 5
        have h_7_c_mod_5 : 7 ^ c ≡ 4 [MOD 5] := by
          rw [← h_eq]
          have : 5 ^ b ≡ 0 [MOD 5] := by
            refine Nat.modEq_zero_iff_dvd.mpr ?_
            exact dvd_pow_self 5 hb
          have : 24 ≡ 4 [MOD 5] := rfl
          rw [show 4 = 4 + 0 by norm_num]
          apply Nat.ModEq.add
          repeat assumption
        -- by observing 7 ^ 4 ≡ 1 mod 5, we deduce 7 ^ c ≡ 7 ^ (c % 4) mod 5
        have h_7_c : 7 ^ c ≡ 7 ^ (c % 4) [MOD 5] := by
          have : c = (c / 4) * 4 + (c % 4) := by exact Eq.symm (Nat.div_add_mod' c 4)
          nth_rw 1 [this]
          rw [pow_add]
          nth_rw 2 [mul_comm]
          have : 7 ^ (4 * (c / 4)) ≡ 1 [MOD 5] := by
            generalize c / 4 = k
            induction' k with k ih
            · norm_num
              rfl
            · rw [mul_add, pow_add]
              norm_num
              have : 2401 ≡ 1 [MOD 25] := by rfl
              rw [show 1 = 1 * 1 by ring]
              exact Nat.ModEq.mul ih this
          nth_rw 2 [show 7 ^ (c % 4) = 1 * 7 ^ (c % 4) by ring]
          apply Nat.ModEq.mul_right
          assumption
        -- enumerating c % 4, we deduce c ≡ 2 mod 4
        have c_eq_2_mod_4 : c ≡ 2 [MOD 4] := by
          suffices h : c % 4 = 2 by exact h
          have _ : c % 4 < 4 := Nat.mod_lt c (by norm_num)
          interval_cases c % 4
          all_goals
            have := Nat.ModEq.trans h_7_c_mod_5.symm h_7_c
            unfold Nat.ModEq at this
            norm_num at this ⊢
        -- so c is even
        have : (4 : ℤ) ∣ c - 2 := by
          apply Int.dvd_sub_of_emod_eq
          norm_cast
        rw [show (4 : ℤ) = 2 * 2 by norm_num] at this
        have : (2 : ℤ) ∣ c - 2 := by exact dvd_of_mul_right_dvd this
        have : (2 : ℤ) ∣ c := by exact dvd_sub_self_right.mp this
        have : Even c := by
          apply (Int.even_coe_nat c).mp
          apply even_iff_two_dvd.mpr this
        -- let c = 2 * n
        obtain ⟨n, hn⟩ := this

        -- observe that 24 = 7^c - 5^b = (7^n - 5^m)(7^n + 5^m)
        have h_24_eq_mul : (24 : ℤ) = (7^n - 5^m) * (7^n + 5^m) := by
          have : (24 : ℤ) = 7^c - 5^b := by linarith
          rw [this, hn, hm]
          ring

        -- since (7^n + 5^m) > 0 we have (7^n - 5^m) > 0
        have h_left_pos : (7^n - 5^m) > (0 : ℤ) := by
          by_contra! h
          have : (7^n + 5^m) > (0 : ℤ) := by
            apply add_pos
            all_goals norm_cast
            exact Nat.pos_of_neZero (7 ^ n)
            exact Nat.pos_of_neZero (5 ^ m)
          have : (7^n - 5^m) * (7^n + 5^m) ≤ (0 : ℤ) := by
            apply Int.mul_nonpos_of_nonpos_of_nonneg
            assumption
            exact Int.le_of_lt this
          linarith
        have h_left_lt_right : (7^n - 5^m : ℤ) < (7^n + 5^m) := by
          suffices h : (- 5^m : ℤ) < 5^m by linarith
          have : 5^m > (0 : ℤ) := by
            norm_cast
            exact Nat.pos_of_neZero (5 ^ m)
          linarith

        -- the factors of 24 are a few possibilities
        have factor_24 {a b : ℤ} (h : 24 = a * b)
          (h1 : a < b) (h2 : 0 < a) :
          (a = 1 ∧ b = 24) ∨ (a = 2 ∧ b = 12) ∨ (a = 3 ∧ b = 8) ∨ (a = 4 ∧ b = 6) := by
          have : b ≤ 24 := by
            by_contra! h
            have : a ≥ 1 := h2
            have : a * b > 1 * 24 := by
              refine Int.mul_lt_mul' h2 h ?h₃ h2
              norm_num
            linarith
          have : b > 0 := by linarith
          have h_dvd : b ∣ 24 := by exact Dvd.intro_left a (id (Eq.symm h))
          have ha_eq: a = 24 / b := by
            refine Int.eq_ediv_of_mul_eq_right ?H1 ?H2
            exact Ne.symm (Int.ne_of_lt this)
            rw [h]; ring
          interval_cases b
          all_goals norm_num at h_dvd
          all_goals
            norm_num at ha_eq
            rw [ha_eq] at h1
            norm_num at h1
          all_goals simp [ha_eq]

        -- checking these cases, the only solution is (4, 2, 2)
        have := factor_24 h_24_eq_mul h_left_lt_right h_left_pos
        rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · -- (7^n - 5^m) = 1, (7^n + 5^m) = 24, impossible
          have : 2 * 7 ^ n = (25 : ℤ) := by
            linear_combination' h1 + h2
          have : (2 : ℤ) ∣ 25 := by exact Dvd.intro (7 ^ n) this
          norm_num at this
        · -- (7^n - 5^m) = 2, (7^n + 5^m) = 12
          -- we have n = m = 1, so b = c = 2, a = 4
          have : 2 * 7 ^ n = 2 * (7 : ℤ) := by
            linear_combination' h1 + h2
          have : 7 ^ n = (7 : ℤ) := by
            apply mul_left_cancel₀ (a := 2) (by norm_num) this
          norm_cast at this
          have hn_eq_1 : n = 1 := by
            apply (Nat.pow_eq_self_iff (show 7 > 1 by norm_num)).mp
            exact this

          have : 2 * 5 ^ m = 2 * (5 : ℤ) := by
            linear_combination' h2 - h1
          have : 5 ^ m = (5 : ℤ) := by
            apply mul_left_cancel₀ (a := 2) (by norm_num) this
          norm_cast at this
          have hm_eq_1 : m = 1 := by
            apply (Nat.pow_eq_self_iff (show 5 > 1 by norm_num)).mp
            exact this

          right; right
          simp [hn, hm, hn_eq_1, hm_eq_1]
        · -- (7^n - 5^m) = 3, (7^n + 5^m) = 8, impossible
          have : 2 * 7 ^ n = (11 : ℤ) := by
            linear_combination' h1 + h2
          have : (2 : ℤ) ∣ 11 := by exact Dvd.intro (7 ^ n) this
          norm_num at this
        · -- (7^n - 5^m) = 4, (7^n + 5^m) = 6, impossible
          have h0 : 2 * 7 ^ n = (10 : ℤ) := by
            linear_combination' h1 + h2
          have h1: (7^n : ℤ) ∣ 10 := Dvd.intro_left 2 h0
          by_cases h : n = 0
          · rw [h] at h0
            norm_num at h0
          have : n > 0 := by exact Nat.zero_lt_of_ne_zero h
          have : (7 : ℤ) ∣ 7 ^ n := by exact dvd_pow_self 7 h
          have : (7 : ℤ) ∣ 10 := by exact Int.dvd_trans this h1
          norm_num at this
    · rintro (h | h | h)
      all_goals simp [h, Nat.factorial]
