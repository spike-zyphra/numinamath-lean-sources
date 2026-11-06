import Mathlib

/- Find all positive integers $n$ such that there exists a prime number $p$, such that

$$
p^{n}-(p-1)^{n}
$$

is a power of 3 .

Note. A power of 3 is a number of the form $3^{a}$ where $a$ is a positive integer. -/
theorem number_theory_605929 :
    {n : ℕ | 0 < n ∧ ∃ p : ℕ, Nat.Prime p ∧ ∃ a : ℕ, 0 < a ∧ p ^ n - (p - 1) ^ n = 3 ^ a} = {2} := by
  -- Break the goal into two parts.
  ext n
  simp
  apply Iff.intro
  . -- First show that the condition implies that n = 2.
    rintro ⟨h₀, p, h₁, a, h₂, h₃⟩
    -- Make a lemma that if 3 ∣ 2 ^ n - 1, then 2 ∣ n.
    have h₄ (m : ℕ) (hm : 3 ∣ 2 ^ m - 1) : 2 ∣ m := by
      rw [<-Nat.modEq_iff_dvd' (by apply Nat.one_le_pow _ _ (by norm_num))] at hm
      symm at hm
      rw [<-ZMod.eq_iff_modEq_nat] at hm
      zify at hm
      rw [pow_eq_one_iff_modEq] at hm
      suffices orderOf (2 : ZMod 3) = 2 by
        simp [this] at hm
        symm at hm
        rw [Nat.modEq_iff_dvd' (by simp)] at hm
        simp_all
      -- Show that orderOf (2 : ZMod 3) = 2.
      apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by norm_cast)
      -- For any prime that divides 2, 2 ^ (2 / p) does not equal 1 modulo 3.
      intro p hp hp'
      rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_two)] at hp'
      simp [hp']
      norm_cast
    by_cases h₅ : p = 2
    . -- Consider the case p = 2. We have 2 ^ n - 1 = 3 ^ a.
      simp [h₅] at h₃
      -- By the lemma above, n is even.
      have hn : 2 ∣ n := by
        apply h₄
        rw [h₃]
        apply dvd_pow_self _ h₂.ne'
      -- Let n = 2s for some s.
      rw [dvd_iff_exists_eq_mul_left] at hn
      obtain ⟨s, rfl⟩ := hn
      -- We have (2 ^ s - 1) * (2 ^ s + 1) = 3 ^ a.
      rw [pow_mul, show 1 = 1 ^ 2 by norm_num, Nat.sq_sub_sq] at h₃
      -- Note that we cannot have both 3 ∣ 2 ^ s + 1 and 3 ∣ 2 ^ s - 1.
      have h₆ : ¬(3 ∣ 2 ^ s + 1 ∧ 3 ∣ 2 ^ s - 1) := by
        by_contra!
        obtain ⟨h₆, h₇⟩ := this
        -- Assume on the contrary that 3 ∣ 2 ^ s - 1 and 3 ∣ 2 ^ s + 1, then 3 ∣ 2, contradiction.
        have : 2 ^ s ≥ 1 := by
          apply Nat.one_le_pow _ _ (by simp)
        rw [show 2 ^ s + 1 = 2 ^ s - 1 + 2 by omega] at h₆
        rw [<-Nat.dvd_add_iff_right h₇] at h₆
        norm_num at h₆
      rw [Classical.not_and_iff_or_not_not] at h₆
      -- Therefore, either 3 ∤ 2 ^ s - 1 or 3 ∤ 2 ^ s + 1.
      cases h₆ with
      | inl h₆ =>
        -- Note that 3 ^ a ∣ (2 ^ s + 1)(2 ^ s - 1) but 3 ∤ 2 ^ s + 1, so 3 ^ a ∣ 2 ^ s - 1.
        have h₇ := @Prime.pow_dvd_of_dvd_mul_left _ _ _ (2 ^ s + 1) (2 ^ s - 1) (Nat.prime_iff.mp Nat.prime_three) a h₆ (by rw [h₃])
        -- We have 2 ^ s + 1 ≤ 2 ^ s - 1, which is impossible.
        have : 2 ^ s - 1 > 0 := by
          by_contra!
          simp_all
          linarith [show 0 < 3 ^ a by positivity]
        have : 2 ^ s + 1 ≤ 2 ^ s - 1 := by
          apply Nat.le_of_dvd this
          calc
            _ ∣ 3 ^ a := by
              rw [<-h₃]
              apply Nat.dvd_mul_right
            _ ∣ 2 ^ s - 1 := h₇
        -- We derive a contradiction from this.
        omega
      | inr h₆ =>
        -- Note that 3 ^ a ∣ (2 ^ s + 1)(2 ^ s - 1) but 3 ∤ 2 ^ s - 1, so 3 ^ a ∣ 2 ^ s + 1.
        have h₇ := @Prime.pow_dvd_of_dvd_mul_right _ _ _ (2 ^ s + 1) (2 ^ s - 1) (Nat.prime_iff.mp Nat.prime_three) a h₆ (by rw [h₃])
        -- We have 2 ^ s + 1 = 3 ^ a, so 2 ^ s - 1 = 1.
        replace h₇ : 3 ^ a = 2 ^ s + 1 := by
          apply Nat.dvd_antisymm h₇
          rw [<-h₃]
          apply Nat.dvd_mul_right
        simp [<-h₇] at h₃
        -- We have 2 ^ s = 2 ^ 1, so s = 1, n = 2, which is the desired solution.
        replace h₃ : 2 ^ s = 2 ^ 1 := by
          omega
        apply Nat.pow_right_injective (by norm_num) at h₃
        simp [h₃]
    . by_cases h₆ : p = 3
      . -- Consider the case p = 3, where 3 ^ n - 2 ^ n = 3 ^ a.
        simp [h₆] at h₃
        -- We have 3 ∣ 3 ^ n - 2 ^ n.
        replace h₃ : 3 ∣ 3 ^ n - 2 ^ n := by
          rw [h₃]
          apply dvd_pow_self _ h₂.ne'
        -- We have 3 ∣ 2 ^ n, which is impossible.
        replace h₃ : 3 ∣ 2 ^ n := by
          rw [Nat.dvd_add_iff_right h₃, Nat.sub_add_cancel]
          apply dvd_pow_self _ h₀.ne'
          rw [Nat.pow_le_pow_iff_left h₀.ne']
          norm_num
        -- We derive a contradiction from this.
        apply Nat.Prime.dvd_of_dvd_pow Nat.prime_three at h₃
        norm_num at h₃
      . -- Suppose now that p ≥ 5.
        -- We have p % 3 = 2.
        have h₇ : p % 3 = 2 := by
          by_contra!
          -- If not, then 3 ∣ p or 3 ∣ p - 1.
          replace this : 3 ∣ p ∨ 3 ∣ p - 1 := by
            omega
          cases this with
          | inl this =>
            -- If 3 ∣ p, then p = 3, which is impossible.
            rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three h₁] at this
            tauto
          | inr this =>
            -- If 3 ∣ p - 1, then we also get 3 ∣ p from the equation, which is impossible.
            replace h₃ : 3 ∣ p ^ n - (p - 1) ^ n := by
              rw [h₃]
              apply dvd_pow_self _ h₂.ne'
            replace this : 3 ∣ (p - 1) ^ n := by
              calc
                3 ∣ p - 1 := this
                _ ∣ (p - 1) ^ n := by
                  apply dvd_pow_self _ (by omega)
            have : 3 ∣ p ^ n := by
              rw [Nat.dvd_add_iff_left this, Nat.sub_add_cancel] at h₃
              tauto
              rw [Nat.pow_le_pow_iff_left h₀.ne']
              omega
            apply Nat.Prime.dvd_of_dvd_pow Nat.prime_three at this
            rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three h₁] at this
            tauto
        -- We prove that n is even.
        have h₈ : 2 ∣ n := by
          -- Examine the original equation modulo 3, we get 2 ^ n ≡ 1 (mod 3).
          apply Nat.eq_add_of_sub_eq (by rw [Nat.pow_le_pow_iff_left h₀.ne']; omega) at h₃
          replace h₃ := congr_arg (· % 3) h₃
          have h₇' : (p - 1) % 3 = 1 := by
            omega
          simp [Nat.add_mod, Nat.pow_mod, h₇, h₇'] at h₃
          norm_num [Nat.zero_pow h₂] at h₃
          -- Apply the lemma proved before to show that 2 ∣ n.
          apply h₄
          omega
        -- Let n = 2k for some k.
        rw [dvd_iff_exists_eq_mul_right] at h₈
        obtain ⟨k, h₈⟩ := h₈
        -- Substitute n = 2k into the original equation, we get (p ^ k - (p - 1) ^ k)(p ^ k + (p - 1) ^ k) = 3 ^ a.
        rw [h₈, mul_comm 2, pow_mul, pow_mul, Nat.sq_sub_sq] at h₃
        -- Note that we cannot have both 3 ∣ p ^ k + (p - 1) ^ k and 3 ∣ p ^ k - (p - 1) ^ k.
        have h₉ : ¬(3 ∣ p ^ k + (p - 1) ^ k ∧ 3 ∣ p ^ k - (p - 1) ^ k) := by
          by_contra!
          obtain ⟨h₉, h₁₀⟩ := this
          -- Assume on the contrary that 3 ∣ p ^ k - (p - 1) ^ k and 3 ∣ p ^ k + (p - 1) ^ k, then 3 ∣ p, contradiction.
          have : (p - 1) ^ k ≤ p ^ k := by
            rw [Nat.pow_le_pow_iff_left (by omega)]
            omega
          rw [show p ^ k + (p - 1) ^ k = p ^ k - (p - 1) ^ k + 2 * (p - 1) ^ k by omega] at h₉
          rw [<-Nat.dvd_add_iff_right h₁₀, Nat.Prime.dvd_mul (Nat.prime_three)] at h₉
          norm_num at h₉
          apply Nat.Prime.dvd_of_dvd_pow Nat.prime_three at h₉
          omega
        -- Therefore, either 3 ∤ p ^ k - (p - 1) ^ k or 3 ∤ p ^ k + (p - 1) ^ k.
        rw [Classical.not_and_iff_or_not_not] at h₉
        cases h₉ with
        | inl h₉ =>
          -- Note that 3 ^ a ∣ (p ^ k + (p - 1) ^ k)(p ^ k - (p - 1) ^ k) but 3 ∤ p ^ k + (p - 1) ^ k, so 3 ^ a ∣ p ^ k - (p - 1) ^ k.
          have h₁₁ := @Prime.pow_dvd_of_dvd_mul_left _ _ _ (p ^ k + (p - 1) ^ k) (p ^ k - (p - 1) ^ k) (Nat.prime_iff.mp Nat.prime_three) a h₉ (by rw [h₃])
          -- We have p ^ k + (p - 1) ^ k ≤ p ^ k - (p - 1) ^ k, which is impossible.
          have : p ^ k + (p - 1) ^ k ≤ p ^ k - (p - 1) ^ k := by
            have : p ^ k - (p - 1) ^ k > 0 := by
              by_contra!
              simp_all
              linarith [show 0 < 3 ^ a by positivity]
            apply Nat.le_of_dvd this
            calc
              _ ∣ 3 ^ a := by
                rw [<-h₃]
                apply Nat.dvd_mul_right
              _ ∣ p ^ k - (p - 1) ^ k := h₁₁
          -- We derive a contradiction from this.
          have : 1 ≤ (p - 1) ^ k := by
            apply Nat.one_le_pow _ _ (by omega)
          omega
        | inr h₉ =>
          -- Note that 3 ^ a ∣ (p ^ k + (p - 1) ^ k)(p ^ k - (p - 1) ^ k) but 3 ∤ p ^ k - (p - 1) ^ k, so 3 ^ a ∣ p ^ k + (p - 1) ^ k.
          have h₁₁ := @Prime.pow_dvd_of_dvd_mul_right _ _ _ (p ^ k + (p - 1) ^ k) (p ^ k - (p - 1) ^ k) (Nat.prime_iff.mp Nat.prime_three) a h₉ (by rw [h₃])
          -- We have 3 ^ a = p ^ k + (p - 1) ^ k, so p ^ k - (p - 1) ^ k = 1.
          replace h₁₁ : 3 ^ a = p ^ k + (p - 1) ^ k := by
            apply Nat.dvd_antisymm h₁₁
            rw [<-h₃]
            apply Nat.dvd_mul_right
          simp [<-h₁₁] at h₃
          by_cases hk : k = 1
          . -- Suppose k = 1, then n = 2, which is the solution we want.
            omega
          . -- Suppose k ≠ 1, then k ≥ 2.
            replace hk : k ≥ 2 := by
              omega
            -- We shall show that p ^ k - (p - 1) ^ k > 1, so we get a contradiction.
            suffices p ^ k - (p - 1) ^ k > 1 by
              linarith only [this, h₃]
            calc
              _ ≥ p ^ 2 - (p - 1) ^ 2 := by
                -- This inequality is equivalent to p ^ 2 * (p ^ (k - 2) - 1) ≥ (p - 1) ^ 2 * ((p - 1) ^ (k - 2) - 1), which is obviously true.
                suffices p ^ 2 * (p ^ (k - 2) - 1) ≥ (p - 1) ^ 2 * ((p - 1) ^ (k - 2) - 1) by
                  iterate 2 rw [Nat.mul_sub, <-Nat.pow_add, mul_one, show 2 + (k - 2) = k by omega] at this
                  zify at this ⊢
                  iterate 2 rw [Int.natCast_sub] at this ⊢
                  linarith
                  all_goals
                    first | rw [Nat.pow_le_pow_iff_left (by omega)] | rw [Nat.pow_le_pow_iff_right (by omega)]
                    omega
                apply Nat.mul_le_mul
                . rw [Nat.pow_le_pow_iff_left (by omega)]
                  omega
                . rw [Nat.sub_le_sub_iff_right (by apply Nat.one_le_pow _ _ (by omega))]
                  apply Nat.pow_le_pow_left
                  omega
              _ = 2 * p - 1 := by
                rw [Nat.sq_sub_sq, Nat.sub_sub_self]
                omega
                exact Nat.Prime.one_le h₁
              _ > 1 := by
                omega
  . -- Now we verify again that n = 2 is possible. Either take p = 2 or 5.
    rintro hn
    simp [hn]
    use 2, Nat.prime_two, 1
    norm_num
