import Mathlib

/- Solve in positive integers the equation $1005^{x}+2011^{y}=1006^{z}$. -/
theorem number_theory_604378 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1006^z = 1005^x + 2011^y) :
    (x, y, z) = (2, 1, 2) := by
    have h1: 2011^y < 1006^z := by
      rw [h]
      suffices 0 < 1005^x by linarith
      positivity
    have t1: y ≥ 1 := by linarith
    have t2: z ≥ 1 := by linarith
    have h2: 1006 < 1006^z := by
      suffices 1006 < 2011^y by linarith
      suffices 2011 ≤ 2011^y by linarith
      nth_rw 1 [← pow_one 2011]
      apply pow_le_pow
      linarith
      linarith
      linarith
    -- 1. proving z ≥ 2 by natural number property
    have h3 : z ≥ 2 := by
      by_contra!
      cases' this with hp hq
      . ring_nf at h2
        tauto
      . ring_nf at hq
        rw [Nat.succ_eq_add_one] at hq
        field_simp at hq
        rw [hq] at t2
        tauto
    -- 2. calc 1005^x mod 4
    have h4 : 1005^x ≡ 1^x [MOD 4] := by
      apply Nat.ModEq.pow
      have hs : 1005 = 4 * 251 + 1 := by norm_num
      rw [hs]
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd]
      norm_num
    rw [one_pow] at h4

    have div_sq : 1006^2 % 4 = 0 := by norm_num
    have div_pow : 1006^z ≡ 0 [MOD 1006 ^2]:= by
      apply Nat.ModEq.symm
      have sq_1006 : 1012036 = 1006 ^ 2 := by norm_num
      rw [Nat.modEq_iff_dvd]
      norm_num
      exact pow_dvd_pow 1006 h3
    apply Nat.ModEq.symm at div_pow
    rw [Nat.modEq_iff_dvd] at div_pow
    norm_num at div_pow
    -- 3. derive 1006^z mod 4
    have h5 : 1006^z ≡ 0 [MOD 4] := by
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd]
      norm_num
      omega

    rw [h] at h5
    have mod_rfl : 2011^y ≡ 2011^y [MOD 4] := by
      exact Nat.ModEq.rfl
    have trans_left : 1005^x + 2011^y ≡ 1 + 2011^y [MOD 4] := by
      exact Nat.ModEq.add h4 mod_rfl
    apply Nat.ModEq.symm at trans_left
    have trans_res : 1 + 2011^y ≡ 0 [MOD 4] := by
      exact Nat.ModEq.trans trans_left h5
    have base_mod_4 : 0 ≡ 1 + 3 [MOD 4] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    have trans_res_1 : 1 + 2011^y ≡ 1 + 3 [MOD 4] := by
      exact Nat.ModEq.trans trans_res base_mod_4
    apply Nat.ModEq.add_left_cancel' at trans_res_1

    have h6 : 2011^y ≡ 3 [MOD 4] := by
      exact trans_res_1
    have t_mod_4 : 2011 ≡ 3 [MOD 4] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    have t_mod_4_pow : 2011^y % 4 = 3^y % 4 := by
      rw [Nat.ModEq.pow y t_mod_4]
    have h6' : 3^y % 4 = 3 % 4 := by
      rw [← t_mod_4_pow]
      exact h6
    -- 4. derive 2011^y mod 4
    -- if y is even, then lhs = 9 ^ k % 4 = 1 ^ k = 1 ≠ 3
    -- hence y is odd
    have h7 : y % 2 ≠ 0 := by
      by_contra!
      have y_even : y ≡ 0 [MOD 2] := by tauto
      rw [Nat.modEq_zero_iff_dvd] at y_even
      rw [dvd_def] at y_even
      cases' y_even with k hk
      rw [hk] at h6'
      rw [pow_mul] at h6'
      norm_num at h6'
      have nine_mod_4 : 9 ≡ 1 [MOD 4] := by
        rw [Nat.modEq_iff_dvd]
        norm_num
      have pow_9 : 9 ^ k % 4 = 1 ^ k % 4 := by
        rw [Nat.ModEq.pow k nine_mod_4]
      rw [pow_9, one_pow] at h6'
      tauto
    have y_options : y % 2 = 0 ∨ y % 2 = 1 := by
      apply Nat.mod_two_eq_zero_or_one

    have y_odd_p : y ≡ 1 [MOD 2] := by
      cases' y_options with h0 h1
      . tauto
      . rw [show 1 = 1 % 2 by norm_num] at h1
        exact h1
    have y_odd_c : y - 1 + 1 ≡ 0 + 1 [MOD 2] := by
      rw [zero_add, Nat.sub_add_cancel]
      tauto
      linarith

    have y_odd: y - 1 ≡ 0 [MOD 2] := by
      exact Nat.ModEq.add_right_cancel' 1 y_odd_c

    rw [Nat.modEq_zero_iff_dvd] at y_odd

    rw [dvd_def] at y_odd
    cases' y_odd with l hl
    have hly : y = 2 * l + 1 := by omega
    have pow_2011 : 4044121 ≡ 1 [MOD 1006] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    have mod_1006_pow : 4044121 ^ l % 1006 = 1 ^ l % 1006 := by
      rw [Nat.ModEq.pow l pow_2011]
    rw [one_pow] at mod_1006_pow
    have mod_1006_pow_mod : 4044121 ^ l ≡ 1 [MOD 1006] := by
      exact mod_1006_pow
    have mod_1006_mul : 4044121 ^ l * 2011 ≡ 1 * 2011 [MOD 1006] := by
      exact Nat.ModEq.mul_right 2011 mod_1006_pow_mod
    have mod_1006_add : 4044121 ^ l * 2011 + 1 ≡ 1 * 2011 + 1 [MOD 1006] := by
      exact Nat.ModEq.add_right 1 mod_1006_mul
    have mod_1006_base :  1 * 2011 + 1 ≡ 0 [MOD 1006] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    have h8 : 2011^y + 1 ≡ 0 [MOD 1006] := by
      rw [hly, pow_add, pow_mul, pow_one]
      rw [show 2011^2 = 4044121 by norm_num]
      exact Nat.ModEq.trans mod_1006_add mod_1006_base

    have tot_mod_1006 : 2011^y + 1005^x ≡ 0 [MOD 1006] := by
      rw [add_comm]
      rw [← h]
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd]
      norm_num
      apply dvd_pow
      norm_num
      linarith

    apply Nat.ModEq.symm at tot_mod_1006
    have x_mod_1006 : 2011^y + 1 ≡ 2011^y + 1005^x [MOD 1006] := by
      exact Nat.ModEq.trans h8 tot_mod_1006
    apply Nat.ModEq.add_left_cancel' at x_mod_1006
    -- 5. derive 1005^x mod 1006, and further prove x is even
    have h9 : 1005^x ≡ 1 [MOD 1006] := by
      exact Nat.ModEq.symm x_mod_1006
    have h10 : x % 2 = 0 := by
      by_contra! odd_x
      have x_options : x % 2 = 0 ∨ x % 2 = 1 := by
        apply Nat.mod_two_eq_zero_or_one
      have x_odd_p : x ≡ 1 [MOD 2] := by
        cases' x_options with h2 h3
        . tauto
        . rw [show 1 = 1 % 2 by norm_num] at h3
          exact h3
      have x_odd_c : x - 1 + 1 ≡ 0 + 1 [MOD 2] := by
        rw [zero_add, Nat.sub_add_cancel]
        tauto
        linarith

      have x_odd: x - 1 ≡ 0 [MOD 2] := by
        exact Nat.ModEq.add_right_cancel' 1 x_odd_c

      rw [Nat.modEq_zero_iff_dvd] at x_odd

      rw [dvd_def] at x_odd
      cases' x_odd with u hu
      have hlx : x = 2 * u + 1 := by omega
      rw [hlx] at h9
      rw [pow_add, pow_mul, pow_one] at h9
      rw [show 1005^2 =1010025 by norm_num] at h9
      have sq_mod_1006 : 1010025 ≡ 1 [MOD 1006] := by
        rw [Nat.modEq_iff_dvd]
        norm_num
      have pow_1006 : 1010025 ^ u % 1006 = 1 ^ u % 1006 := by
        rw [Nat.ModEq.pow u sq_mod_1006]
      have pow_1006_mod : 1010025 ^ u ≡ 1 ^ u [MOD 1006] := by
        exact pow_1006
      rw [one_pow] at pow_1006_mod
      have pow_1006_mul : 1010025 ^ u * 1005 ≡  1 * 1005 [MOD 1006] := by
        exact Nat.ModEq.mul_right 1005 pow_1006_mod
      apply Nat.ModEq.symm at pow_1006_mul
      have trans_1006 : 1 * 1005 ≡  1 [MOD 1006] := by
        exact Nat.ModEq.trans pow_1006_mul h9
      apply Nat.ModEq.symm at trans_1006
      rw [Nat.modEq_iff_dvd] at trans_1006
      norm_num at trans_1006

    have t_mod_8 : 1005 ≡ 5 [MOD 8] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    have t_mod_8_pow : 1005 ^ x % 8 = 5 ^ x % 8 := by
      rw [Nat.ModEq.pow x t_mod_8]
    have t_mod_8_left : 1005 ^x ≡ 5 ^ x [MOD 8] := by
      exact t_mod_8_pow
    have x_even : x ≡ 0 [MOD 2] := by tauto
    rw [Nat.modEq_zero_iff_dvd] at x_even
    rw [dvd_def] at x_even
    cases' x_even with k hk
    have t_mod_8_right : 5^x ≡ 1 [MOD 8] := by
      rw [hk, pow_mul]
      rw [show 5^2 = 25 by norm_num]
      have t_mod_3 : 25 ≡ 1 [MOD 8] := by
        rw [Nat.modEq_iff_dvd]
        norm_num
      have pow_25 : 25 ^ k % 8 = 1 ^ k % 8 := by
        rw [Nat.ModEq.pow k t_mod_3]
      rw [one_pow] at pow_25
      exact pow_25

    -- by x is even
    have h11 : 1005^x ≡ 1 [MOD 8] := by
      exact Nat.ModEq.trans t_mod_8_left t_mod_8_right
    -- by y is odd
    have y_mod_8 : 2011 ≡ 3 [MOD 8] := by
      rw [Nat.modEq_iff_dvd]
      norm_num
    have y_mod_8_pow : 2011^y % 8 = 3 ^ y % 8 := by
      rw [Nat.ModEq.pow y y_mod_8]
    have y_mod_8_left : 2011^y ≡ 3^y [MOD 8] := by
      exact y_mod_8_pow
    have y_mod_8_right : 3^y ≡ 3 [MOD 8] := by
      rw [hly, pow_add, pow_mul]
      rw [show 3 ^ 2 = 9 by norm_num]
      rw [pow_one]
      have nine_mod_8 : 9 ≡ 1 [MOD 8] := by
        rw [Nat.modEq_iff_dvd]
        norm_num
      have pow_9_8 : 9 ^ l % 8 = 1 ^ l % 8 := by
        rw [Nat.ModEq.pow l nine_mod_8]
      rw [one_pow] at pow_9_8
      have pow_9_mod : 9 ^ l ≡ 1 [MOD 8] := by tauto
      have pow_9_mul : 9 ^ l * 3 ≡ 1 * 3 [MOD 8] := by
        exact Nat.ModEq.mul_right 3 pow_9_mod
      rw [one_mul] at pow_9_mul
      tauto

    have h12 : 2011^y ≡ 3 [MOD 8] := by
      exact Nat.ModEq.trans y_mod_8_left y_mod_8_right
    -- by trans rule
    have tot_mod_8 : 1005^x + 2011^y ≡ 4 [MOD 8] := by
      exact Nat.ModEq.add h11 h12

    -- 6. derive 1006^z mod 8, and determine z = 2
    have h13 : 1006^z ≡ 4 [MOD 8] := by
      rw [h]
      exact tot_mod_8
    have bound_z : z ≤ 2 := by
      by_contra!
      have bound_z_1 : z ≥ 3 := by
        tauto
      -- prove 8 | 1006^z
      have div_pow_3 : 1006^z ≡ 0 [MOD 1006 ^3]:= by
        apply Nat.ModEq.symm
        have sq_1006 : 1012036 = 1006 ^ 2 := by norm_num
        rw [Nat.modEq_iff_dvd]
        norm_num
        exact pow_dvd_pow 1006 bound_z_1
      apply Nat.ModEq.symm at div_pow_3
      rw [Nat.modEq_iff_dvd] at div_pow_3
      norm_num at div_pow_3
      have div_cube : 1006^z ≡ 0 [MOD 8] := by
        apply Nat.ModEq.symm
        rw [Nat.modEq_iff_dvd]
        norm_num
        omega
      apply Nat.ModEq.symm at div_cube
      have div_final : 0 ≡ 4 [MOD 8] := by
        exact Nat.ModEq.trans div_cube h13
      rw [Nat.modEq_iff_dvd] at div_final
      norm_num at div_final

    have bound_z_2 : z ≠ 1 := by
      by_contra!
      rw [this] at h13
      tauto

    have tz : z = 2 := by
      omega

    -- 7. finally, determine y by inequality and calc x
    have ine_y : 2011 ^ y < 1006 ^z := by
      rw [h]
      linarith
    rw [tz] at ine_y
    have pow_y_bound : 2011^y < 2011^2 := by
      linarith
    have bound_base : 1 < 2011 := by norm_num
    have bound_iff : 2011^y < 2011^2 ↔ y < 2 := by
      exact Nat.pow_lt_pow_iff_right bound_base
    have y_bound : y < 2 := by
      tauto
    have ty : y = 1 := by
      omega
    have tx : x = 2 := by
      rw [tz, ty] at h
      norm_num at h
      have txx : 1012036 = 1005 ^2 + 2011:= by norm_num
      rw [txx] at h
      field_simp at h
      rw [h]

    rw [tx, ty, tz]
