import Mathlib

/-Let $N$ be an integer such that $18 \le N \le 998$.
Theorem: For any positive integer $n$ such that $n + 17 \le N$, there exists an integer $m$ in the set of 18 consecutive integers $\{n, n+1, \dots, n+17\}$ such that $m$ is divisible by the sum of its digits.-/
theorem number_theory_637317 (N : ℕ) (hN : 18 ≤ N ∧ N ≤ 998) (n : ℕ) (hn : n > 0 ∧ n + 17 ≤ N) :
  ∃ m ∈ Set.Icc n (n + 17), m % (Nat.digits 10 m).sum = 0 := by
  -- Show there exists$ m$ in $[n, n+17]$ divisible by $18$.
  have h_exists_18 : ∃ m ∈ Set.Icc n (n + 17), m % 18 = 0 := by
    let m := n + (18 - n % 18) % 18
    have hm_Icc : m ∈ Set.Icc n (n + 17) := by simp [Set.Icc];omega
    have hm_dvd : m % 18 = 0 := by simp [m, Nat.dvd_iff_mod_eq_zero];omega
    exact ⟨m, hm_Icc, hm_dvd⟩

  -- Pick such an $m$ and analyze its digit sum.
  obtain ⟨m, hm_Icc, hm_18⟩ := h_exists_18
  have h_m_pos : m > 0 := by linarith [hm_Icc.1]
  have h_m_le_998 : m ≤ 998 := by linarith [hN.2, hn, hm_Icc.2]
  have h_mod_9 : 9 ∣ m := by omega
  have h_digit_sum_mod_9 : (Nat.digits 10 m).sum % 9 = 0 := by
    exact Nat.dvd_iff_mod_eq_zero.mp ((Nat.nine_dvd_iff m).mp h_mod_9)
  have h_digit_sum_vals : (Nat.digits 10 m).sum = 9 ∨ (Nat.digits 10 m).sum = 18 := by
    have h_digit_sum_le_26 : (Nat.digits 10 m).sum ≤ 26 := by
      have h_digits : (Nat.digits 10 m).length ≤ 3 := by
        have : (Nat.digits 10 m).length ≤ (Nat.digits 10 998).length := by
          exact Nat.le_digits_len_le 10 m 998 h_m_le_998
        norm_num at this
        exact this
      have h_digit_bound : ∀ d ∈ Nat.digits 10 m, d ≤ 9 := by
        intro d hd
        have h_lt_10 : d < 10 := Nat.digits_lt_base (by norm_num : 1 < 10) hd
        nlinarith
      have h_sum_bound : (Nat.digits 10 m).sum ≤ 27 := by
        have : (Nat.digits 10 m).sum ≤ (Nat.digits 10 m).length * 9 := by
          apply List.sum_le_card_nsmul
          exact h_digit_bound
        nlinarith
      -- We need to show that if the sum of digits is $27$, then m must be $999$
      have h_sum_ne : (Nat.digits 10 m).sum ≠ 27 := by
        intro h
        have h_len_eq_3 : (Nat.digits 10 m).length = 3 := by
          have : (Nat.digits 10 m).sum ≤ (Nat.digits 10 m).length * 9 := by
            apply List.sum_le_card_nsmul
            exact h_digit_bound
          nlinarith
        -- Prove that each digit must be $9$ to achieve a sum of $27$ with exactly three digits.
        have h_digit_eq : ∀ d ∈ Nat.digits 10 m, d = 9 := by
          intro d hd
          by_contra h_d_ne_9
          have h_digit_bound' : d ≤ 9 := by
            have h_lt_10 : d < 10 := Nat.digits_lt_base (by norm_num : 1 < 10) hd
            nlinarith
          have h_d_le_8 : d ≤ 8 := by omega
          have h_sum_lt_27 : (Nat.digits 10 m).sum < 27 := by
            calc
              (Nat.digits 10 m).sum = d + List.sum (List.erase (Nat.digits 10 m) d) := by rw [← List.sum_erase hd]
              _ ≤ 8 + 9 * 2 := by
                have : List.sum (List.erase (Nat.digits 10 m) d) ≤ List.length (List.erase (Nat.digits 10 m) d) * 9 := by
                  apply List.sum_le_card_nsmul
                  intro x hx
                  have h_x_in : x ∈ Nat.digits 10 m := List.erase_subset d (Nat.digits 10 m) hx
                  exact h_digit_bound x h_x_in
                have : List.length (List.erase (Nat.digits 10 m) d) = 2 := by
                  have h_len : List.length (List.erase (Nat.digits 10 m) d) = (Nat.digits 10 m).length - 1 := by
                    apply List.length_erase_of_mem hd
                  rw [h_len_eq_3] at h_len
                  norm_num [h_len]
                linarith
              _ = 26 := by norm_num
              _ < 27 := by norm_num
          linarith
        have : m = 999 := by
          have h_digits_eq : Nat.digits 10 m = List.replicate 3 9 := by
            rw [← h_len_eq_3]
            apply List.eq_replicate_of_mem
            exact h_digit_eq
          have : Nat.digits 10 999 = List.replicate 3 9 := by simp
          rw [← this] at h_digits_eq
          exact Nat.digits_inj_iff.mp h_digits_eq
        linarith
      omega
    -- Prove that the sum of digits is positive, as $m > 0$ implies at least one non-zero digit.
    have h_digit_sum_pos : (Nat.digits 10 m).sum > 0 := by
      by_contra h_npos
      have : (Nat.digits 10 m).sum = 0 := by omega
      have : m = 0 := by
        have : ∀ y ∈ Nat.digits 10 m, y = 0 := by
          apply List.sum_eq_zero_iff.mp
          exact this
        have : Nat.digits 10 m = List.replicate (Nat.digits 10 m).length 0 := by
          apply List.eq_replicate_iff.mpr
          constructor
          · rfl
          · exact this
        have : Nat.ofDigits 10 (Nat.digits 10 m) = 0 := by
          rw [this]
          induction (Nat.digits 10 m).length with
          | zero => simp
          | succ m ih => simp [List.replicate, Nat.ofDigits]; rw [ih]
        rw [Nat.ofDigits_digits] at this
        exact this
      linarith
    -- Derive sum of digits can only be $9$ or $18$.
    have h_digit_sum_multiple_9 : (Nat.digits 10 m).sum % 9 = 0 := h_digit_sum_mod_9
    interval_cases h : (Nat.digits 10 m).sum <;> norm_num at h_digit_sum_multiple_9 ⊢

  -- Show $m$ is divisible by its digit sum.
  have h_divisible : m % (Nat.digits 10 m).sum = 0 := by
    cases h_digit_sum_vals with
    | inl h =>
      rw [h]
      exact Nat.dvd_iff_mod_eq_zero.mp h_mod_9
    | inr h =>
      rw [h]
      exact hm_18

  -- Conclude
  exact ⟨m, hm_Icc, h_divisible⟩
