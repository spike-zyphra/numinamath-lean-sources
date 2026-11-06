import Mathlib

/- For naturals numbers a b and c, a mod b is equal to c iff b is zero and a is
  equal to c, or c is less than b and there exists some k such that a = b * k + c. -/
lemma mod_eq_iff {a b c : Nat} :
    a % b = c ↔ (b = 0 ∧ a = c) ∨ (c < b ∧ Exists fun k => a = b * k + c) :=
  ⟨fun h =>
    if w : b = 0 then
      .inl ⟨w, by simpa [w] using h⟩
    else
      .inr ⟨by subst h; exact Nat.mod_lt a (Nat.zero_lt_of_ne_zero w),
        a / b, by subst h; exact (Nat.div_add_mod a b).symm⟩,
   by
     rintro (⟨rfl, rfl⟩ | ⟨w, h, rfl⟩)
     · simp_all
     · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt w]⟩

/- 10. Among $1,2,3,4, \cdots, 1000$, the numbers that can be written in the form $a^{2}-b^{2}+1(a, b \in \mathbf{N})$ and are not divisible by 3 are $\qquad$ in number. -/
theorem number_theory_111326 [DecidablePred (fun n => (∃ a b, n = a^2 - b^2 + 1))] :
    ((Finset.Icc 1 1000).filter (fun n => (∃ a b, n = a^2 - b^2 + 1) ∧ ¬3 ∣ n)).card = 501 := by

      -- For every n, we have some a and b such that n = a ^ 2 - b ^ 2 + 1 iff n ≢ 3 (mod 4)
      have squares_iff_not_mod : ∀ x ∈ (Finset.Icc 1 1000),
        (fun n => ∃ a b, n = a ^ 2 - b ^ 2 + 1) x ↔ (¬· ≡ 3 [MOD 4]) x := by
          -- simplify
          simp only [Finset.mem_filter, Finset.mem_Icc, and_congr_right_iff, and_imp]
          intro n _ _
          -- show both directions
          constructor
          -- let n = a ^ 2 - b ^ 2 + 1
          · rintro ⟨a, b, rfl⟩
            convert_to ¬a ^ 2 - b ^ 2 + 1 ≡ 2 + 1 [MOD 4]

            -- assume the opposite
            by_contra mod

            -- then a ^ 2 - b ^ 2 ≡ 2 (mod 4)
            apply Nat.ModEq.add_right_cancel' at mod

            -- note that squares mod 4 are either 0 or 1
            have sq_mod_four : ∀ n, (n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1) := by
              intro n
              mod_cases n % 4
              all_goals
              · norm_num [Nat.ModEq] at H ⊢
                norm_num [Nat.pow_mod, H]

            -- consider when a ^ 2 ≤ b ^ 2
            by_cases hh : a ^ 2 ≤ b ^ 2
            -- then a ^ 2 - b ^ 2 = 0
            · have eq_zero : a ^ 2 - b ^ 2 = 0 := Nat.sub_eq_zero_of_le hh

              -- which is a contradiction
              norm_num [eq_zero, Nat.ModEq] at mod

            -- so we have a ^ 2 ≡ 2 + b ^ 2 (mod 4)
            apply Nat.ModEq.add_right (b ^ 2) at mod
            have cancelled : a ^ 2 - b ^ 2 + b ^ 2 = a ^ 2 := by omega
            rw [cancelled] at mod

            -- then we consider cases of a ^ 2 (mod 4) and b ^ 2 (mod 4)
            norm_num [Nat.ModEq, Nat.add_mod] at mod
            rcases sq_mod_four a with a_0 | a_1
            · rcases sq_mod_four b with b_0 | b_1
              · norm_num [a_0, b_0] at mod
              · norm_num [a_0, b_1] at mod
            · rcases sq_mod_four b with b_0 | b_1
              · norm_num [a_1, b_0] at mod
              · norm_num [a_1, b_1] at mod
          -- consider when n ≢ 3 (mod 4)
          · intro aa
            -- if n ≡ b (mod 4), then there's some k such that 4 * k + b = n
            have mod_four_exists : ∀ {n b}, n ≡ b [MOD 4] → b < 4 → ∃ k, 4 * k + b = n := by
              intro n b H bh
              norm_num [Nat.ModEq, mod_eq_iff] at H
              obtain ⟨_, k, kh⟩ := H
              exists k
              omega

            -- consider n modulo 4
            mod_cases n % 4
            -- let n ≡ 0 (mod 4)
            · obtain ⟨k, kh⟩ := mod_four_exists H (by norm_num)
              -- then a = 2 * k, b = 2 * k - 1 works
              exists 2*k, 2*k - 1

              -- we have that k * 2 is positive
              have : 1 ≤ k * 2 := by
                suffices : k ≠ 0; omega
                -- assume k is 0
                by_contra eq_zero
                -- then n is 0
                norm_num [eq_zero] at kh
                -- but that's impossible, because n is positive
                linarith
              -- simplify
              have eq_one : (2 * k - (2 * k - 1)) = 1 := by omega
              rw [←kh, Nat.sq_sub_sq, eq_one]
              ring_nf
              omega

            -- let n ≡ 1 (mod 4)
            · obtain ⟨k, kh⟩ := mod_four_exists H (by norm_num)
              rw [←kh]
              by_cases k_eq_zero : k = 0
              -- consider when k = 0, then a = 0 and b = 0 works
              · exists 0, 0
                norm_num [k_eq_zero]

              -- else, a = k + 1, b = k - 1 works
              exists k + 1, k - 1

              -- simplify
              have eq_two : (k + 1 - (k - 1)) = 2 := by omega
              rw [Nat.sq_sub_sq, eq_two]
              ring_nf
              omega
            -- let n ≡ 2 (mod 4)
            · obtain ⟨k, kh⟩ := mod_four_exists H (by norm_num)
              -- then a = 2 * k + 1, b = 2 * k works
              exists 2*k + 1, 2*k

              -- simplify
              have eq_one : 2 * k + 1 - 2 * k = 1 := by omega
              rw [←kh, Nat.sq_sub_sq, eq_one]
              ring_nf
            -- n ≡ 3 (mod 4) doesn't work
            · contradiction

      -- split up set
      rw [Finset.filter_and]

      -- rewrite using mod
      rw [Finset.filter_congr squares_iff_not_mod]

      -- consider complements
      rw [Finset.filter_not]
      rw [Finset.filter_not]

      -- x is divisible by 3 iff x ≡ 0 (mod 3)
      have equiv : ∀ x ∈ (Finset.Icc 1 1000), (Dvd.dvd 3) x ↔ (x ≡ 0 [MOD 3]) := by
        intro x xh
        exact Nat.modEq_zero_iff_dvd.symm

      -- rewrite to use mod
      rw [Finset.filter_congr equiv]

      -- simplify set cardinalities
      rw [←Finset.sdiff_union_distrib, Finset.card_sdiff, Finset.card_union, ←Finset.filter_and]

      -- There are 250 numbers in [1, 1000] that are congruent to 3, mod 4
      have three_mod_four : ((Finset.Icc 1 1000).filter (· ≡ 3 [MOD 4])).card = 250 := by
        have count := @Nat.Ico_filter_modEq_card 1 1001 4 (by omega) 3
        norm_num at count
        simpa only [show 250 = ((250 : ℕ) : ℤ) by omega, Nat.cast_inj] using count

      rw [three_mod_four]

      -- There are 333 numbers in [1, 1000] that are congruent to 0, mod 3
      have zero_mod_four : ((Finset.Icc 1 1000).filter (· ≡ 0 [MOD 3]) ).card = 333 := by
        have count := @Nat.Ico_filter_modEq_card 1 1001 3 (by omega) 0
        norm_num at count
        simpa only [show 333 = ((333 : ℕ) : ℤ) by omega, Nat.cast_inj] using count

      rw [zero_mod_four]

      have equiv : ∀ x ∈ (Finset.Icc 1 1000), (x ≡ 3 [MOD 4] ∧ x ≡ 0 [MOD 3]) ↔ x ≡ 3 [MOD 12] := by
        intro x xh
        constructor
        -- let x ≡ 3 (mod 4) and x ≡ 0 (mod 3)
        · intro ⟨aa, bb⟩
          -- 4 and 3 are coprime
          have coprime : Nat.Coprime 4 3 := by decide

          -- the chinese reminder theorem gives us the value y such that x ≡ y [MOD 12]
          have chinese_rem := Nat.chineseRemainder_modEq_unique coprime aa bb

          -- the value y is 3
          have eq_three : (Nat.chineseRemainder coprime 3 0).1 = 3 := by
            norm_num [Nat.chineseRemainder, Nat.chineseRemainder']
            ring_nf
            have gcd_eq : Nat.xgcd 4 3 = (1, -1) := by norm_num [Nat.xgcd, Nat.xgcdAux]
            norm_num [gcd_eq]
            exact rfl
          -- so we have x ≡ 3 (mod 12)
          simpa only [Nat.reduceMul, eq_three] using chinese_rem
        -- given x ≡ 3 (mod 12)
        · intro aa
          -- then we have x ≡ 3 (mod 3 * 4)
          convert_to x ≡ 3 [MOD 3 * 4] at aa
          -- so x ≡ 3 (mod 4)
          have mod_four := Nat.ModEq.of_mul_left 3 aa
          -- and x ≡ 3 (mod 3), i.e. x ≡ 0 (mod 3)
          have mod_three := Nat.ModEq.of_mul_right 4 aa
          exact ⟨mod_four, mod_three⟩

      rw [Finset.filter_congr equiv]

      -- There are 84 numbers in [1, 1000] that are congruent to 3, mod 12
      have three_mod_twelve : ((Finset.Icc 1 1000).filter (· ≡ 3 [MOD 12])).card = 84 := by
        have count := @Nat.Ico_filter_modEq_card 1 1001 12 (by omega) 3
        norm_num at count
        simpa only [show 84 = ((84 : ℕ) : ℤ) by omega, Nat.cast_inj] using count
      rw [three_mod_twelve]
      norm_num

      -- Every set we've manipulated was a subset of [1, 1000], so our operations were valid
      rw [← Finset.filter_or]
      exact Finset.filter_subset _ _