import Mathlib

/-
  Find all positive integers n such that the number $A_n = \frac{2 ^{4n+2}}{65}$ is
  a) an integer
  b) a prime
  (Answer: a) when n % 3 = 1, b) never)
-/
theorem number_theory_605347 (n : ℕ) :
  ((∃ (n' : ℤ), n' = ((2 : ℝ) ^ (4 * n + 2) + 1) / 65) ↔ n ≡ 1 [ZMOD 3]) ∧
  ((∃ (n' : ℤ), Prime n' ∧ n' = ((2 : ℝ) ^ (4 * n + 2) + 1) / 65) ↔ False) := by

    -- we show that 2 ^ 12k ≡ 1 [ZMOD 13]
    have lem1 (k : ℕ) : 2 ^ (12 * k) ≡ 1 [ZMOD 13] := by
      induction k
      case zero => simp
      case succ k ih =>
        rw [mul_add, pow_add]
        simp
        have : 4096 ≡ 1 [ZMOD 13] := rfl
        have := Int.ModEq.mul ih this
        simp at this
        exact this

    -- with the above lemma, we show that 2 ^ (4 * k + 2) ≡ 2 ^ (4 * r + 2) [ZMOD 13]
    -- whenever k ≡ r [ZMOD 3]
    have lem2 (k : ℕ) : 2 ^ (4 * k + 2) ≡ 2 ^ (4 * (k % 3) + 2) [ZMOD 13] := by
      have : k = (k / 3) * 3 + k % 3 := by exact Eq.symm (Nat.div_add_mod' k 3)
      nth_rw 1 [this]
      rw [mul_add,
        show 4 * (k / 3 * 3) = 12 * (k / 3) by rw [mul_comm, mul_assoc, mul_comm]; norm_num,
        add_assoc,
        pow_add
      ]
      nth_rw 2 [← one_mul (2 ^ (4 * (k % 3) + 2))]
      apply Int.ModEq.mul_right
      apply lem1 (k / 3)

    -- the following lemma will be used for deriving contradictions
    have lem_not_prime (a b : ℤ) (ha : a > 1) (hb : b > 1) : ¬ Prime (a * b) := by
      have h1 : ¬ IsUnit a := by
        intro h
        rcases Int.isUnit_iff.mp h with rfl | rfl
        <;> linarith
      have h2 : ¬ IsUnit b := by
        intro h
        rcases Int.isUnit_iff.mp h with rfl | rfl
        <;> linarith
      intro h
      apply prime_mul_iff.mp at h
      simp_all only [gt_iff_lt, and_false, false_and, or_self]

    -- Now we prove part a). we state it as a separated theorem because
    -- we will need it in part b)
    have theorem_part_a (n : ℕ) :
      ((∃ (n' : ℤ), n' = ((2 : ℝ) ^ (4 * n + 2) + 1) / 65) ↔ n ≡ 1 [ZMOD 3]) := by
        constructor
        · -- necessity of n ≡ 1 [ZMOD 3]
          rintro ⟨n', hn'⟩
          field_simp at hn'
          norm_cast at hn'
          -- suppose A_n is an integer, we must have 65 is a factor of the denumerator
          have : (65 : ℤ) ∣ 2 ^ (4 * n + 2) + 1 := by
            use n'
            nth_rw 2 [mul_comm]
            rw [hn']
            norm_cast

          -- as 65 = 5 * 13, we deduce 13 is a factor of 2 ^ (4 * n + 2) + 1
          rw [show (65 : ℤ) = 5 * 13 by norm_num] at this
          have dvd_by_13 : (13 : ℤ) ∣ 2 ^ (4 * n + 2) + 1 := by exact dvd_of_mul_left_dvd this
          have mod_13_eq_zero := Int.modEq_zero_iff_dvd.mpr dvd_by_13
          unfold Int.ModEq at mod_13_eq_zero

          -- by lem2, 2 ^ (4 * n + 2) + 1 ≡ 2 ^ (4 * (n % 3) + 2) + 1 [ZMOD 13]
          rw [Int.add_emod, lem2 n] at mod_13_eq_zero

          have : n % 3 < 3 := by
            refine Nat.mod_lt n ?_
            norm_num

          unfold Int.ModEq
          norm_num; norm_cast

          -- let r = n % 3, we analysis by cases of r = 0, 1, 2
          generalize n % 3 = r at *
          interval_cases r
          · -- r = 0, contradiction
            norm_num at mod_13_eq_zero
          · -- r = 1
            rfl
          · -- r = 2, contradiction
            norm_num at mod_13_eq_zero
        · -- sufficiency of n ≡ 1 [ZMOD 3]
          intro hn_mod_3
          use ((2 : ℤ) ^ (4 * n + 2) + 1) / 65
          field_simp
          norm_cast
          suffices h : ((2 : ℤ) ^ (4 * n + 2) + 1) / 65 * 65 = 2 ^ (4 * n + 2) + 1 by
            norm_cast at h
          -- to show A_n is integer, we only need to show 65 is a factor of the denumerator
          apply Int.ediv_mul_cancel

          -- as 65 = 5 * 13, we show both 5 and 13 are factors of denumerator
          rw [show (65 : ℤ) = 5 * 13 by norm_num]
          have : IsCoprime 5 (13 : ℤ) := by norm_num
          apply IsCoprime.mul_dvd this
          · -- show 5 ∣ 2 ^ (4 * n + 2) + 1
            rw [show (5 : ℤ) = 4 + 1 by norm_num]
            rw [show 4 * n + 2 = 2 * (2 * n + 1) by ring]
            rw [pow_mul, show 2 ^ 2 = (4 : ℤ) by norm_num]
            nth_rw 2 [show (1 : ℤ) = 1 ^ (2 * n + 1) by ring]
            norm_cast
            refine Odd.nat_add_dvd_pow_add_pow 4 1 ?h'.h
            simp
          · -- show 13 ∣ 2 ^ (4 * n + 2) + 1, using lem2
            have : n % 3 = 1 := by
              exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Int.ModEq.symm hn_mod_3)))
            suffices h : 2 ^ (4 * n + 2) + 1 ≡ 0 [ZMOD 13] by
              exact Int.dvd_of_emod_eq_zero h
            suffices h : 2 ^ (4 * n + 2) ≡ -1 [ZMOD 13] by
              calc
                2 ^ (4 * n + 2) + 1 ≡ -1 + 1 [ZMOD 13] := by exact Int.ModEq.add h rfl
                _ ≡ 0 [ZMOD 13] := by norm_num
            unfold Int.ModEq
            rw [lem2 n, this]
            norm_num

    -- this is the main part of the proof
    constructor
    · -- part a), we have finished in theorem_part_a
      exact theorem_part_a n
    · -- part b)
      constructor
      · -- we show that n' := A_n cannot be a prime
        intro ⟨n', ⟨hp_n', hn'⟩⟩
        -- as A_n is an integer, we deduce n ≡ 1 [ZMOD 3]
        have hn_mod_3 := (theorem_part_a n).mp ⟨n', hn'⟩
        apply Int.ModEq.symm at hn_mod_3
        -- so write n = 1 + 3 * k' 
        rw [Int.modEq_iff_add_fac] at hn_mod_3
        obtain ⟨k, hk⟩ := hn_mod_3
        field_simp at hn'
        norm_cast at hn'
        have hn' : n' * 65 = (2 : ℤ) ^ (4 * n + 2) + 1 := by
          norm_cast
        have : n = 1 + 3 * (k.toNat) := by
          apply Int.ofNat_inj.mp
          have : k ≥ 0 := by
            by_contra! h
            have : (n : ℤ) ≥ 0 := by norm_cast; exact Nat.zero_le n
            rw [hk] at this
            linarith
          simp [this]
          exact hk
        let k' := k.toNat
        have : n = 1 + 3 * k' := by unfold k'; exact this
        rw [this] at hn'

        -- we factor (2 : ℤ) ^ (4 * (1 + 3 * k') + 2) + 1 as 
        -- (2 ^ (4 * k' + 2) + 1) * (2 ^ (8 * k' + 4) - 2 ^ (4 * k' + 2) + 1)
        rw [
          show (2 : ℤ) ^ (4 * (1 + 3 * k') + 2) + 1 = (2 ^ (4 * k' + 2) + 1) * (2 ^ (8 * k' + 4) - 2 ^ (4 * k' + 2) + 1) by ring
        ] at hn'

        -- first we rule the possibility that k' = 0
        -- as then n' = 1 is not a prime
        by_cases hk' : k' = 0
        · rw [hk'] at hn'
          norm_num at hn'
          have : n' ≠ 1 := by exact Prime.ne_one hp_n'
          contradiction

        -- in the following, k' ≠ 0, so k' > 0
        have k'gt0 : k' > 0 := by
          exact Nat.zero_lt_of_ne_zero hk'

        -- the first factor 2 ^ (4k' + 2) is always divided by 5
        have fst_factor_dvd_by_5 : 5 ∣ (2 : ℤ) ^ (4 * k' + 2) + 1 := by
          rw [show 4 * k' + 2 = 2 * (2 * k' + 1) by ring]
          rw [pow_mul, show 2 ^ 2 = (4 : ℤ) by norm_num, show (5 : ℤ) = 4 + 1 by norm_num]
          nth_rw 2 [show (1 : ℤ) = 1 ^ (2 * k' + 1) by ring]
          norm_cast
          apply Odd.nat_add_dvd_pow_add_pow 4 1
          simp

        have fst_factor_rw : (2 : ℤ) ^ (4 * k' + 2) + 1 = (2 ^ (4 * k' + 2) + 1) / 5 * 5 := by
          exact Eq.symm (Int.ediv_mul_cancel fst_factor_dvd_by_5)

        -- we divide into 3 cases for k' % 3 = 0, 1, 2
        have : k' % 3 < 3 := Nat.mod_lt k' (by norm_num)
        rw [show (2 : ℤ) ^ (8 * k' + 4) = (2 ^ (4 * k' + 2)) ^ 2 by ring] at hn'
        interval_cases h : k' % 3
        · -- k' % 3 = 0
          rw [fst_factor_rw] at hn'
          -- we show that 13 is a factor of the second factor, using lem2
          have : (13 : ℤ) ∣ ((2 ^ (4 * k' + 2)) ^ 2 - 2 ^ (4 * k' + 2) + 1) := by
            suffices h : ((2 ^ (4 * k' + 2)) ^ 2 - 2 ^ (4 * k' + 2) + 1) ≡ 0 [ZMOD 13]
              by exact Int.dvd_of_emod_eq_zero h
            unfold Int.ModEq
            rw [Int.add_emod, Int.sub_emod, pow_two, Int.mul_emod]
            rw [lem2 k', h]
            norm_num
          -- write the second factor as b
          generalize hb : (((2 : ℤ) ^ (4 * k' + 2)) ^ 2 - 2 ^ (4 * k' + 2) + 1) = b at *
          have : b = b / 13 * 13 := by exact Eq.symm (Int.ediv_mul_cancel this)
          rw [this] at hn'

          -- we deduce n' = (2 ^ (4 * k' + 2) + 1) / 5 * (b / 13)
          have : (2 ^ (4 * k' + 2) + 1) / 5 * 5 * (b / 13 * 13) = ((2 ^ (4 * k' + 2) + 1) / 5) * (b / 13) * 65 := by ring
          rw [this] at hn'
          simp at hn'

          -- and both factors are > 1
          have : ((2 : ℤ) ^ (4 * k' + 2) + 1) / 5 > 1 := by
            norm_cast at fst_factor_dvd_by_5 ⊢
            apply (Nat.lt_div_iff_mul_lt' (fst_factor_dvd_by_5) 1).mpr
            have : k' ≥ 1 := by exact k'gt0
            have : 2 ^ (4 * k' + 2) ≥ 2 ^ (4 * 1 + 2) := by
              apply Nat.pow_le_pow_right
              norm_num
              linarith
            norm_num at this ⊢
            linarith
          generalize ((2 : ℤ) ^ (4 * k' + 2) + 1) / 5 = a at *
          have : b / 13 > 1 := by
            rw [← hb]
            apply Int.lt_ediv_of_mul_lt
            · norm_num
            · rw [hb]
              assumption
            norm_num
            nlinarith
          generalize b / 13 = c at *

          -- so their product is not a prime
          have : ¬ Prime n' := by
            rw [hn']
            apply lem_not_prime a c
            <;> assumption
          contradiction
        · -- k' % 3 = 1
          -- first we rule out the possibility that k' = 1
          -- as then n' = 4033 is not a prime
          by_cases hk'eq1 : k' = 1
          · rw [hk'eq1] at hn'
            have : ((2 : ℤ) ^ (4 * 1 + 2) + 1) = 65 := by norm_num
            rw [this] at hn'
            nth_rw 2 [mul_comm] at hn'
            apply (Int.mul_eq_mul_right_iff (by norm_num)).mp at hn'
            norm_num at hn'
            have : ¬Prime n' := by
              rw [hn']
              norm_num
            contradiction

          -- in the following k' ≠ 1, so k' > 1
          have k'gt1 : k' > 1 := by
            exact Nat.lt_of_le_of_ne k'gt0 fun a ↦ hk'eq1 (id (Eq.symm a))

          -- write the second factor as b
          generalize hb : (((2 : ℤ) ^ (4 * k' + 2)) ^ 2 - 2 ^ (4 * k' + 2) + 1) = b at *

          -- we show that 13 is a factor of the first factor
          have fst_factor_dvd_by_13 : (13 : ℤ) ∣ (2 ^ (4 * k' + 2) + 1) := by
            suffices h : 2 ^ (4 * k' + 2) + 1 ≡ 0 [ZMOD 13]
              by exact Int.dvd_of_emod_eq_zero h
            unfold Int.ModEq
            rw [Int.add_emod]
            rw [lem2 k', h]
            norm_num

          -- so 5 * 13 = 65 divides first factor
          have : IsCoprime 5 (13 : ℤ) := by norm_num
          have dvd_by_65 : (13 * 5 : ℤ) ∣ (2 ^ (4 * k' + 2) + 1) := by
            exact IsCoprime.mul_dvd (id (IsCoprime.symm this)) fst_factor_dvd_by_13 fst_factor_dvd_by_5
          norm_num at dvd_by_65

          -- let the first factor be a, we have n' = a / 65 * b
          generalize ha : ((2 : ℤ) ^ (4 * k' + 2) + 1) = a at *
          have : a = a / 65 * 65 := by exact Eq.symm (Int.ediv_mul_cancel dvd_by_65)
          rw [this, show a / 65 * 65 * b = a / 65 * b * 65 by ring] at hn'
          simp at hn'

          -- clearly b > 1 as k' > 0
          have : b > 1 := by
            rw [← hb]
            norm_num
            refine lt_self_pow₀ ?h ?hm
            · suffices h : 2 ≤ (2 : ℤ) ^ (4 * k' + 2) by exact h
              nth_rw 1 [show (2 : ℤ) = 2 ^ 1 by norm_num]
              apply pow_le_pow_right₀
              norm_num
              linarith
            norm_num
          -- also a / 65 > 1 as k' > 1
          have : a / 65 > 1 := by
            apply Int.lt_ediv_of_mul_lt
            · norm_num
            · exact dvd_by_65
            rw [← ha]
            rw [show (1 * 65 : ℤ) = 2 ^ 6 + 1 by norm_num]
            apply Int.add_lt_add_right ?H 1
            calc
              (2 : ℤ) ^ 6 < 2 ^ (4 * 2 + 2) := by norm_num
              _ ≤ 2 ^ (4 * k' + 2) := by
                apply pow_le_pow_right₀
                norm_num
                linarith

          -- so their product is not a prime
          have : ¬ Prime n' := by
            rw [hn']
            apply lem_not_prime (a / 65) b
            <;> assumption
          contradiction
        · -- k' % 3 = 2, this is exactly same as k' % 3 = 0
          rw [fst_factor_rw] at hn'
          have : (13 : ℤ) ∣ ((2 ^ (4 * k' + 2)) ^ 2 - 2 ^ (4 * k' + 2) + 1) := by
            suffices h : ((2 ^ (4 * k' + 2)) ^ 2 - 2 ^ (4 * k' + 2) + 1) ≡ 0 [ZMOD 13]
              by exact Int.dvd_of_emod_eq_zero h
            unfold Int.ModEq
            rw [Int.add_emod, Int.sub_emod, pow_two, Int.mul_emod]
            rw [lem2 k', h]
            norm_num
          generalize hb : (((2 : ℤ) ^ (4 * k' + 2)) ^ 2 - 2 ^ (4 * k' + 2) + 1) = b at *
          have : b = b / 13 * 13 := by exact Eq.symm (Int.ediv_mul_cancel this)
          rw [this] at hn'
          have : (2 ^ (4 * k' + 2) + 1) / 5 * 5 * (b / 13 * 13) = ((2 ^ (4 * k' + 2) + 1) / 5) * (b / 13) * 65 := by ring
          rw [this] at hn'
          simp at hn'
          have : ((2 : ℤ) ^ (4 * k' + 2) + 1) / 5 > 1 := by
            norm_cast at fst_factor_dvd_by_5 ⊢
            apply (Nat.lt_div_iff_mul_lt' (fst_factor_dvd_by_5) 1).mpr
            have : k' ≥ 1 := by exact k'gt0
            have : 2 ^ (4 * k' + 2) ≥ 2 ^ (4 * 1 + 2) := by
              apply Nat.pow_le_pow_right
              norm_num
              linarith
            norm_num at this ⊢
            linarith
          generalize ((2 : ℤ) ^ (4 * k' + 2) + 1) / 5 = a at *
          have : b / 13 > 1 := by
            rw [← hb]
            apply Int.lt_ediv_of_mul_lt
            · norm_num
            · rw [hb]
              assumption
            norm_num
            nlinarith
          generalize b / 13 = c at *
          have : ¬ Prime n' := by
            rw [hn']
            apply lem_not_prime a c
            <;> assumption
          contradiction
      simp
