import Mathlib

/- 27. (USS 1) Find all natural numbers $n$ for which every natural number whose decimal representation has $n-1$ digits 1 and one digit 7 is prime. -/
theorem number_theory_24310 :
    {n : ℕ | 0 < n ∧ ∀ m, ((Nat.digits 10 m).length = n ∧ ∃ k ∈ Finset.range n, (Nat.digits 10 m)[k]! = 7 ∧ ∀ j ∈ Finset.range n, j ≠ k → (Nat.digits 10 m)[j]! = 1) → Nat.Prime m} = {1, 2} := by
  ext n
  constructor
  . -- First show that the condition implies that n = 1, 2.
    contrapose
    -- Now we assume that n > 2 and show that there exists such number not satisfying the condition.
    intro hn
    simp only [Set.mem_setOf]
    push_neg
    intro hn'
    replace hn : n > 2 := by
      simp at hn
      omega
    clear hn'
    by_cases h₀ : 3 ∣ n
    . -- First suppose that 3 ∣ n, we may consider the sum of digits of respective number.
      -- Take m = 111...117.
      use Nat.ofDigits 10 ([7] ++ List.replicate (n - 1) 1)
      -- Show that m is recovered by Nat.digits.
      have h₁ : (Nat.digits 10 (Nat.ofDigits 10 ([7] ++ List.replicate (n - 1) 1))) = [7] ++ List.replicate (n - 1) 1 := by
        rw [Nat.digits_ofDigits _ (by norm_num)]
        . -- Verify that each digit is less than 10.
          intro l hl
          simp at hl
          omega
        . -- Verify that the list is non-empty.
          simp
          rw [List.getLast_cons (by simp; omega), List.getLast_replicate]
          norm_num
      rw [h₁]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      . -- Verify that the number of digits of m is n.
        simp [Nat.sub_add_cancel (show 1 ≤ n by omega)]
      . -- Show that there is a unique digit 7 and the other digits are all 1.
        use 0
        simp [show 0 < n by omega]
        intro j hj hj'
        replace hj' : 1 ≤ j := by
          omega
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj'
        rw [List.getElem?_cons_succ, List.getElem?_replicate_of_lt (by omega)]
        simp
      . -- Show that m is not a prime.
        intro hp
        -- It suffices to show that 3 ∣ m
        suffices 3 ∣ Nat.ofDigits 10 ([7] ++ List.replicate (n - 1) 1) by
          rw [Nat.prime_dvd_prime_iff_eq (Nat.prime_three) hp] at this
          replace this := congr_arg (Nat.digits 10 ·) this
          simp at this
          rw [<-@List.singleton_append _ 7, h₁] at this
          simp at this
        -- Show that 3 ∣ m, which is basically m ≡ 7 + (n - 1) ≡ 0 (mod 3).
        rw [Nat.three_dvd_iff, h₁]
        simp
        omega
    . -- Now suppose that 3 ∤ n.
      -- Divide the cases using modulo 6.
      replace h₀ : n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases h₀ with (h₀ | h₀ | h₀ | h₀)
      . -- Case n % 6 = 1.
        -- Take m = 111...1117.
        use Nat.ofDigits 10 ([7] ++ List.replicate (n - 1) 1)
        -- Show that m is recovered by Nat.digits.
        have h₁ : (Nat.digits 10 (Nat.ofDigits 10 ([7] ++ List.replicate (n - 1) 1))) = [7] ++ List.replicate (n - 1) 1 := by
          rw [Nat.digits_ofDigits _ (by norm_num)]
          . -- Verify that each digit is less than 10.
            intro l hl
            simp at hl
            omega
          . -- Verify that the list is non-empty.
            simp
            rw [List.getLast_cons (by simp; omega), List.getLast_replicate]
            norm_num
        rw [h₁]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        . -- Verify that the number of digits of m is n.
          simp [Nat.sub_add_cancel (show 1 ≤ n by omega)]
        . -- Show that there is a unique digit 7 and the other digits are all 1.
          use 0
          simp [show 0 < n by omega]
          intro j hj hj'
          replace hj' : 1 ≤ j := by
            omega
          obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj'
          rw [List.getElem?_cons_succ, List.getElem?_replicate_of_lt (by omega)]
          simp
        . -- Show that m is not a prime.
          intro hp
          -- It suffices to show that 7 ∣ m
          suffices 7 ∣ Nat.ofDigits 10 ([7] ++ List.replicate (n - 1) 1) by
            rw [Nat.prime_dvd_prime_iff_eq (by decide) hp] at this
            replace this := congr_arg (Nat.digits 10 ·) this
            simp at this
            nth_rw 2 [<-List.singleton_append] at this
            rw [h₁] at this
            simp [show n - 1 ≠ 0 by omega] at this
          -- Show that 7 ∣ m, since we can separate the last digit and 7 ∣ 111111.
          have h₂ := Nat.div_add_mod n 6
          rw [h₀] at h₂
          -- Let k such that n = 6k + 1.
          set k := n / 6 with hk
          rw [show n - 1 = 6 * k by omega]
          clear_value k
          clear h₁ hp n hn h₀ h₂ hk
          -- Prove by induction that 7 ∣ Nat.ofDigits 10 ([7] ++ List.replicate (6 * k) 1).
          induction' k with k hk
          . -- Base case k = 0.
            simp
          . -- Inductive case.
            rw [mul_add, List.replicate_add, <-List.append_assoc, Nat.ofDigits_append]
            apply Nat.dvd_add hk
            norm_num [Nat.ofDigits]
            calc
              _ ∣ 111111 := by
                -- The key is that 7 ∣ 111111.
                norm_num [Nat.ofDigits]
              _ ∣ 10 ^ (6 * k + 1) * 111111 := by
                apply Nat.dvd_mul_left
      . -- Case n % 6 = 2.
        replace hn : n ≥ 8 := by
          omega
        -- Take m = 11...171111.
        use Nat.ofDigits 10 ([1, 1, 1, 1, 7, 1, 1, 1] ++ List.replicate (n - 8) 1)
        -- Show that m is recovered by Nat.digits.
        have h₁ : (Nat.digits 10 (Nat.ofDigits 10 ([1, 1, 1, 1, 7, 1, 1, 1] ++ List.replicate (n - 8) 1))) = [1, 1, 1, 1, 7, 1, 1, 1] ++ List.replicate (n - 8) 1 := by
          rw [Nat.digits_ofDigits _ (by norm_num)]
          . -- Verify that each digit is less than 10.
            intro l hl
            simp at hl
            omega
          . -- Verify that the list is non-empty.
            simp
            by_cases h₁ : n = 8
            . simp [h₁]
            . rw [List.getLast_cons (by simp; omega), List.getLast_replicate]
              norm_num
        rw [h₁]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        . -- Verify that the number of digits of m is n.
          simp
          omega
        . -- Show that there is a unique digit 7 and the other digits are all 1.
          use 4
          refine ⟨?_, ?_, ?_⟩
          . simp
            omega
          . simp
          . intro j hj hj'
            simp at hj
            by_cases hj'' : j < 8
            . rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simp [hj''])]
              interval_cases j
              <;> simp at hj' ⊢
            . rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by push_neg at hj''; simp [hj'']), List.getElem?_replicate_of_lt (by simp; omega)]
              simp
        . -- Show that m is not a prime.
          intro hp
          -- It suffices to show that 7 ∣ m
          suffices 7 ∣ Nat.ofDigits 10 ([1, 1, 1, 1, 7, 1, 1, 1] ++ List.replicate (n - 8) 1) by
            rw [Nat.prime_dvd_prime_iff_eq (by decide) hp] at this
            replace this := congr_arg (Nat.digits 10 ·) this
            simp at this hp h₁
            simp [h₁] at this
          -- Show that 7 ∣ m, since we have 7 ∣ 11171111 and 7 ∣ 111111.
          have h₂ := Nat.div_add_mod n 6
          rw [h₀] at h₂
          -- Let k such that n = 6k + 8.
          set k := n / 6 - 1 with hk
          rw [<-Nat.sub_add_cancel (show 1 ≤ n / 6 by omega), <-hk] at h₂
          rw [show n - 8 = 6 * k by omega]
          clear_value k
          clear h₁ hp n hn h₀ h₂ hk
          -- Prove by induction that 7 ∣ Nat.ofDigits 10 ([1, 1, 1, 1, 7, 1, 1, 1] ++ List.replicate (6 * k) 1).
          induction' k with k hk
          . -- Base case k = 0.
            norm_num [Nat.ofDigits]
          . -- Inductive case.
            rw [mul_add, List.replicate_add, <-List.append_assoc, Nat.ofDigits_append]
            apply Nat.dvd_add hk
            norm_num [Nat.ofDigits]
            calc
              _ ∣ 111111 := by
                -- The key is that 7 ∣ 111111.
                norm_num [Nat.ofDigits]
              _ ∣ 10 ^ (6 * k + 8) * 111111 := by
                apply Nat.dvd_mul_left
      . -- Case n % 6 = 4.
        by_cases hn' : n = 4
        . -- Suppose n = 4.
          -- Take m = 1711, which is not a prime.
          use 1711
          simp [hn', show ¬Nat.Prime 1711 by native_decide]
          -- There is a unique digit 7.
          use 2
          simp
          -- Verify that there all other digits are 1.
          intro j hj hj'
          interval_cases j
          <;> simp at hj' ⊢
        . -- Now n > 4, so n ≥ 10.
          replace hn : n ≥ 10 := by
            omega
          -- Take m = 111...1711111.
          use Nat.ofDigits 10 ([1, 1, 1, 1, 1, 7, 1, 1, 1, 1] ++ List.replicate (n - 10) 1)
          -- Show that m is recovered by Nat.digits.
          have h₁ : (Nat.digits 10 (Nat.ofDigits 10 ([1, 1, 1, 1, 1, 7, 1, 1, 1, 1] ++ List.replicate (n - 10) 1))) = [1, 1, 1, 1, 1, 7, 1, 1, 1, 1] ++ List.replicate (n - 10) 1 := by
            rw [Nat.digits_ofDigits _ (by norm_num)]
            . -- Verify that each digit is less than 10.
              intro l hl
              simp at hl
              omega
            . -- Verify that the list is non-empty.
              simp
              by_cases h₁ : n = 10
              . simp [h₁]
              . rw [List.getLast_cons (by simp; omega), List.getLast_replicate]
                norm_num
          rw [h₁]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          . -- Verify that the number of digits of m is n.
            simp
            omega
          . -- Show that there is a unique digit 7 and the other digits are all 1.
            use 5
            refine ⟨?_, ?_, ?_⟩
            . simp
              omega
            . simp
            . intro j hj hj'
              simp at hj
              by_cases hj'' : j < 10
              . rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simp [hj''])]
                interval_cases j
                <;> simp at hj' ⊢
              . rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by push_neg at hj''; simp [hj'']), List.getElem?_replicate_of_lt (by simp; omega)]
                simp
          . -- Show that m is not a prime.
            by_contra! hp
            -- It suffices to show that 7 ∣ m.
            suffices 7 ∣ Nat.ofDigits 10 ([1, 1, 1, 1, 1, 7, 1, 1, 1, 1] ++ List.replicate (n - 10) 1) by
              rw [Nat.prime_dvd_prime_iff_eq (by decide) hp] at this
              replace this := congr_arg (Nat.digits 10 ·) this
              simp at this hp h₁
              simp [h₁] at this
            -- Show that 7 ∣ m, since we have 7 ∣ 1111711111 and 7 ∣ 111111.
            have h₂ := Nat.div_add_mod n 6
            rw [h₀] at h₂
            -- Let k such that n = 6k + 10.
            set k := n / 6 - 1 with hk
            rw [<-Nat.sub_add_cancel (show 1 ≤ n / 6 by omega), <-hk] at h₂
            rw [show n - 10 = 6 * k by omega]
            clear_value k
            clear h₁ hp n hn hn' h₀ h₂ hk
            -- Prove by induction that 7 ∣ Nat.ofDigits 10 ([1, 1, 1, 1, 1, 7, 1, 1, 1, 1] ++ List.replicate (6 * k) 1).
            induction' k with k hk
            . -- Base case k = 0.
              norm_num [Nat.ofDigits]
            . -- Inductive case.
              rw [mul_add, List.replicate_add, <-List.append_assoc, Nat.ofDigits_append]
              apply Nat.dvd_add hk
              norm_num [Nat.ofDigits]
              calc
                _ ∣ 111111 := by
                  -- The key is that 7 ∣ 111111.
                  norm_num [Nat.ofDigits]
                _ ∣ 10 ^ (6 * k + 10) * 111111 := by
                  apply Nat.dvd_mul_left
      . -- Case n % 6 = 5.
        replace hn : n ≥ 5 := by
          omega
        -- Take m = 1...1711.
        use Nat.ofDigits 10 ([1, 1, 7, 1, 1] ++ List.replicate (n - 5) 1)
        -- Show that m is recovered by Nat.digits.
        have h₁ : (Nat.digits 10 (Nat.ofDigits 10 ([1, 1, 7, 1, 1] ++ List.replicate (n - 5) 1))) = [1, 1, 7, 1, 1] ++ List.replicate (n - 5) 1 := by
          rw [Nat.digits_ofDigits _ (by norm_num)]
          . -- Verify that each digit is less than 10.
            intro l hl
            simp at hl
            omega
          . -- Verify that the list is non-empty.
            simp
            by_cases h₁ : n = 5
            . simp [h₁]
            . rw [List.getLast_cons (by simp; omega), List.getLast_replicate]
              norm_num
        rw [h₁]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        . -- Verify that the number of digits of m is n.
          simp
          omega
        . -- Show that there is a unique digit 7 and the other digits are all 1.
          use 2
          refine ⟨?_, ?_, ?_⟩
          . simp
            omega
          . simp
          . intro j hj hj'
            simp at hj
            by_cases hj'' : j < 5
            . rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simp [hj''])]
              interval_cases j
              <;> simp at hj' ⊢
            . rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by push_neg at hj''; simp [hj'']), List.getElem?_replicate_of_lt (by simp; omega)]
              simp
        . -- Show that m is not a prime.
          by_contra! hp
          -- It suffices to show that 7 ∣ m.
          suffices 7 ∣ Nat.ofDigits 10 ([1, 1, 7, 1, 1] ++ List.replicate (n - 5) 1) by
            rw [Nat.prime_dvd_prime_iff_eq (by decide) hp] at this
            replace this := congr_arg (Nat.digits 10 ·) this
            simp at this hp h₁
            simp [h₁] at this
          -- Show that 7 ∣ m, since we have 7 ∣ 11711 and 7 ∣ 111111.
          have h₂ := Nat.div_add_mod n 6
          rw [h₀] at h₂
          -- Let k such that n = 6k + 5.
          set k := n / 6 with hk
          rw [show n - 5 = 6 * k by omega]
          clear_value k
          clear h₁ hp n hn h₀ h₂ hk
          -- Prove by induction that 7 ∣ Nat.ofDigits 10 ([1, 1, 7, 1, 1] ++ List.replicate (6 * k) 1).
          induction' k with k hk
          . -- Base case k = 0.
            norm_num [Nat.ofDigits]
          . -- Inductive case.
            rw [mul_add, List.replicate_add, <-List.append_assoc, Nat.ofDigits_append]
            apply Nat.dvd_add hk
            norm_num [Nat.ofDigits]
            calc
              _ ∣ 111111 := by
                -- The key is that 7 ∣ 111111.
                norm_num [Nat.ofDigits]
              _ ∣ 10 ^ (6 * k + 5) * 111111 := by
                apply Nat.dvd_mul_left
  . -- Show that for n = 1, 2 the condition is satisfied.
    intro hn
    simp at hn
    rcases hn with (hn | hn)
    . -- Case n = 1.
      simp [hn]
      intro m h₀ h₁
      -- We have m = 7, which is clearly a prime.
      obtain ⟨m', h₀⟩ := List.length_eq_one.mp h₀
      simp [h₀] at h₁
      have h₂ := Nat.ofDigits_digits 10 m
      simp [h₀] at h₂
      rw [<-h₂, h₁]
      decide
    . -- Case n = 2.
      simp [hn]
      intro m h₀ k h₁ h₂ h₃
      -- We either have m = 17 or m = 71, which are both primes.
      obtain ⟨a', b', h₀⟩ := List.length_eq_two.mp h₀
      interval_cases k
      . -- Case m = 17.
        specialize h₃ 1 (by norm_num) (by norm_num)
        simp [h₀] at h₂ h₃
        have h₄ := Nat.ofDigits_digits 10 m
        simp [h₀, h₂, h₃, Nat.ofDigits] at h₄
        rw [<-h₄]
        decide
      . -- Case m = 71.
        specialize h₃ 0 (by norm_num) (by norm_num)
        simp [h₀] at h₂ h₃
        have h₄ := Nat.ofDigits_digits 10 m
        simp [h₀, h₂, h₃, Nat.ofDigits] at h₄
        rw [<-h₄]
        decide
