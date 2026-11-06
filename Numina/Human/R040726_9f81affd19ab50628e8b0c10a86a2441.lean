import Mathlib

/- Déterminer tous les triplets d'entiers ( $a, b, \mathfrak{n}$ ) strictement positifs vérifiant:

$$
a!+b!=2^{n}
$$ -/
theorem number_theory_607287 (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (h : Nat.factorial a + Nat.factorial b = 2 ^ n) :
    (a, b, n) = (1, 1, 1) ∨ (a, b, n) = (2, 2, 2) ∨ (a, b, n) = (2, 3, 3) ∨
    (a, b, n) = (3, 2, 3) := by
      -- helper facts
      have fac3 : Nat.factorial 3 = 6 := by
        rw [Nat.factorial_succ]
        norm_num
      have n_ne_0: n ≠ 0 := by
        by_contra! n_eq_0
        rw [n_eq_0] at hn
        tauto
      have p3 : Prime 3 := by
        have np3 : Nat.Prime 3 := Nat.fact_prime_three.out
        rw [Nat.prime_iff] at np3
        tauto
      have not_three_dvd_pow_two: ¬(3 ∣ 2^n) := by
        by_contra! three_dvd_two_pow
        rw [Prime.dvd_pow_iff_dvd] at three_dvd_two_pow
        tauto
        exact p3
        tauto
      have h_pow_even : Even (2^n) := by
            rw [Nat.even_pow]
            apply And.intro
            . norm_num
            . tauto
      have mod2 : 2 ≡ 2 [MOD 4] := by
            rw [Nat.modEq_iff_dvd]
            tauto

      have a_cases : a = 1 ∨ a = 2 ∨ a ≥ 3 := by
        omega
      rcases a_cases with (a_eq_1 | a_eq_2 | a_ge_3)
      -- a = 1
      case inl =>
        rw [a_eq_1] at h
        norm_num at h
        -- b! is odd => b = 1
        have b_cases : b = 1 ∨ b ≥ 2 := by
          omega
        rcases b_cases with (b_eq_1 | b_ge_2)
        case inl =>
          -- a = 1, b = 1
          rw [b_eq_1] at h
          norm_num at h
          nth_rw 1 [show 2 = 2 ^ 1 by norm_num] at h
          apply Nat.pow_right_injective at h
          have ans1 : (a, b, n) = (1, 1, 1)  := by
            rw [a_eq_1, b_eq_1]
            rw [h]
          tauto
          norm_num

        case inr =>
          apply Nat.dvd_factorial at b_ge_2
          have h_even : Even (Nat.factorial b) := by
            rw [Nat.even_iff]
            exact Nat.mod_eq_zero_of_dvd b_ge_2
          have h_odd : ¬Even (1 + Nat.factorial b) := by
            rw [Nat.not_even_iff_odd]
            exact Even.one_add h_even

          rw [h] at h_odd
          tauto
          positivity
      -- a = 2
      case inr.inl =>
        rw [a_eq_2] at h
        norm_num at h
        have b_cases : b = 1 ∨ b = 2 ∨ b = 3 ∨ b ≥ 4 := by
          omega
        rcases b_cases with (b_eq_1 | b_eq_2 | b_eq_3 | b_ge_4)
        case inl =>
          -- a = 2, b = 1, pass
          rw [b_eq_1] at h
          norm_num at h
          have h1 : 2^n % 2 = 0 := by
            field_simp
            tauto
          rw [←h] at h1
          tauto
        case inr.inl =>
          -- a = 2, b = 2, pass
          rw [b_eq_2] at h
          norm_num at h
          rw [show 4 = 2^2 by norm_num] at h
          apply Nat.pow_right_injective at h
          have ans2 : (a, b, n) = (2, 2, 2) := by
            rw [a_eq_2, b_eq_2, ← h]
          tauto
          tauto

        case inr.inr.inl =>
          -- a = 2, b = 3, pass
          rw [b_eq_3, fac3] at h
          norm_num at h
          rw [show 8 = 2^3 by norm_num] at h
          apply Nat.pow_right_injective at h
          have ans3 :  (a, b, n) = (2, 3, 3) := by
            rw [a_eq_2, b_eq_3, ← h]
          tauto
          tauto
        case inr.inr.inr =>
          -- b >= 4, impossible
          -- 2 + 4! = 2 ^ n
          apply Nat.dvd_factorial at b_ge_4
          have n_ge_2 : n ≥ 2 := by
            by_contra! n_le_2
            have n_eq_1: n = 1 := by
              omega
            rw [n_eq_1] at h
            norm_num at h
            have fac_gt_0 : Nat.factorial b ≠ 0 := by
              exact Nat.factorial_ne_zero b
            omega

          have n_div_4 : 2^n ≡ 0 [MOD 4] := by
            rw [Nat.modEq_zero_iff_dvd]
            rw [show 4 = 2 ^ 2 by norm_num]
            rw [ge_iff_le] at n_ge_2
            exact Nat.pow_dvd_pow 2 n_ge_2

          have fac_b_div : Nat.factorial b ≡ 0 [MOD 4] := by
            rw [Nat.modEq_zero_iff_dvd]
            exact b_ge_4

          have left_mod_4 : 2 + Nat.factorial b ≡ 2 [MOD 4] := by
            exact Nat.ModEq.add mod2 fac_b_div
          rw [h] at left_mod_4
          apply Nat.ModEq.symm at left_mod_4
          have trans_res : 2 ≡ 0 [MOD 4] := by
            exact Nat.ModEq.trans left_mod_4 n_div_4
          rw [Nat.modEq_iff_dvd] at trans_res
          tauto
          positivity

      -- a >= 3
      case inr.inr =>
        have b_cases : b = 1 ∨ b = 2 ∨ b ≥ 3 := by
          omega
        rcases b_cases with (b_eq_1 | b_eq_2 | b_ge_3)
        case inl =>
          -- b = 1 => a = 1, same as first case
          rw [b_eq_1] at h
          norm_num at h
          have a_ge_2 : a ≥ 2 := by
            omega
          apply Nat.dvd_factorial at a_ge_2
          have h_even : Even (Nat.factorial a) := by
            rw [Nat.even_iff]
            exact Nat.mod_eq_zero_of_dvd a_ge_2
          have h_odd : ¬Even (1 + Nat.factorial a) := by
            rw [Nat.not_even_iff_odd]
            exact Even.one_add h_even
          rw [add_comm] at h
          rw [h] at h_odd
          tauto
          positivity

        case inr.inl =>
          -- b = 2 => a = 3 (o) or a >= 4 (x)
          have aa_cases: a = 3 ∨ a ≥ 4 := by
            omega
          rcases aa_cases with (a_eq_3 | a_ge_4)
          case inl =>
            -- b = 2, a = 3 pass
            rw [a_eq_3, b_eq_2, fac3] at h
            norm_num at h
            rw [show 8 = 2^3 by norm_num] at h
            apply Nat.pow_right_injective at h
            have ans3 :  (a, b, n) = (3, 2, 3) := by
              rw [a_eq_3, b_eq_2, ← h]
            tauto
            tauto

          case inr =>
            -- b = 2, a >= 4, impossible
            rw [b_eq_2] at h
            norm_num at h
            apply Nat.dvd_factorial at a_ge_4
            have n_ge_2 : n ≥ 2 := by
              by_contra! n_le_2
              have n_eq_1: n = 1 := by
                omega
              rw [n_eq_1] at h
              norm_num at h
              have fac_gt_0 : Nat.factorial a ≠ 0 := by
                exact Nat.factorial_ne_zero a
              omega
            have n_div_4 : 2^n ≡ 0 [MOD 4] := by
              rw [Nat.modEq_zero_iff_dvd]
              rw [show 4 = 2 ^ 2 by norm_num]
              rw [ge_iff_le] at n_ge_2
              exact Nat.pow_dvd_pow 2 n_ge_2
            have fac_a_div : Nat.factorial a ≡ 0 [MOD 4] := by
              rw [Nat.modEq_zero_iff_dvd]
              exact a_ge_4

            have left_mod_4 : 2 + Nat.factorial a ≡ 2 [MOD 4] := by
              exact Nat.ModEq.add mod2 fac_a_div
            rw [add_comm] at h
            rw [h] at left_mod_4
            apply Nat.ModEq.symm at left_mod_4
            have trans_res : 2 ≡ 0 [MOD 4] := by
              exact Nat.ModEq.trans left_mod_4 n_div_4
            rw [Nat.modEq_iff_dvd] at trans_res
            tauto
            positivity


        case inr.inr =>
          -- impossible cases, 3 | 2 ^ n
          apply Nat.dvd_factorial at a_ge_3
          apply Nat.dvd_factorial at b_ge_3
          have h3 : 3 ∣ Nat.factorial a + Nat.factorial b := by
            apply dvd_add
            · exact a_ge_3
            · exact b_ge_3
          rw [h] at h3

          tauto
          positivity
          positivity
