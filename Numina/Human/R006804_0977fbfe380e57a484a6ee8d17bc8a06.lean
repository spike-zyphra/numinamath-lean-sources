import Mathlib

-- Lemma: Prove that $x ≡ (Nat.digits 10 x).sum [MOD 9]$.
lemma digit_sum_dvd_9 (x : ℕ) : 9 ∣ x - (Nat.digits 10 x).sum := by
  have h_sum_le : (Nat.digits 10 x).sum ≤ x := Nat.digit_sum_le 10 x
  have h_mod_eq : x ≡ (Nat.digits 10 x).sum [MOD 9] := Nat.modEq_nine_digits_sum x
  exact (Nat.modEq_iff_dvd' h_sum_le).mp h_mod_eq.symm

/-Let $k_0$ be the integer $4444$. Let $N_0 = k_0^{k_0}$. Let $A_0$ be the sum of the digits of $N_0$ in base 10. Let $B_0$ be the sum of the digits of $A_0$ in base 10. Let $C_0$ be the sum of the digits of $B_0$ in base 10 (the problem states $C_0=7$).
Let $k$ be a positive integer. Suppose $k \equiv k_0 \pmod{54}$. Let $N = k^k$. Let $D_N$ be the number of digits of $N$ when written in base 10. Suppose $D_N < 111112$.
Let $A$ be the sum of the digits of $N$. Let $B$ be the sum of the digits of $A$. Let $C$ be the sum of the digits of $B$.
Show that $C = C_0$ (i.e. $C=7$).-/
theorem number_theory_641324 (k : ℕ) (hk : k ≡ 4444 [MOD 54])
    (N : ℕ) (hN : N = k ^ k) (D_N : ℕ) (hD_N : D_N = (Nat.digits 10 N).length)
    (hD_N_bound : D_N < 111112) (A B C : ℕ)
    (hA : A = (Nat.digits 10 N).sum) (hB : B = (Nat.digits 10 A).sum)
    (hC : C = (Nat.digits 10 B).sum) :
    C = 7 := by
  -- Prove $N ≡ A ≡ B ≡ C (mod 9)$.
  have h_sum_le_N: (Nat.digits 10 N).sum ≤ N  := Nat.digit_sum_le 10 N
  have h_sum_le_A: (Nat.digits 10 A).sum ≤ A := Nat.digit_sum_le 10 A
  have h_sum_le_B: (Nat.digits 10 B).sum ≤ B := Nat.digit_sum_le 10 B
  have h_N_A : 9 ∣ N - A := by rw [hA];exact digit_sum_dvd_9 N
  have h_A_B : 9 ∣ A - B := by rw [hB]; exact digit_sum_dvd_9 A
  have h_B_C : 9 ∣ B - C := by rw [hC]; exact digit_sum_dvd_9 B
  have h_N_C : 9 ∣ N - C := by
    have : N - C = (N - A) + (A - B) + (B - C) := by omega
    omega

  -- Compute $k ≡ 7 (mod 9)$.
  have h_k_mod_9 : k ≡ 7 [MOD 9] := by
    have h_div : 9 ∣ 54 := by norm_num
    have h_eq:  k ≡ 4444 [MOD 9] := Nat.ModEq.of_dvd h_div hk
    have h_k0_mod_9 : 4444 ≡ 7 [MOD 9] := by tauto
    tauto

  -- Compute $N ≡ 7 (mod 9)$.
  have h_N_mod_9 : N ≡ 7 [MOD 9] := by
    rw [hN]
    have h_k_mod_6 : k ≡ 4 [MOD 6] := by
      have h_div : 6 ∣ 54 := by norm_num
      have h_eq:  k ≡ 4444 [MOD 6] := Nat.ModEq.of_dvd h_div hk
      have h_k0_mod_9 : 4444 ≡ 4 [MOD 6] := by tauto
      tauto
    have h_7_powers : 7 ^ 4 ≡ 7 [MOD 9] := by tauto
    have h_pow_mod_eq: k ^ k ≡ 7 ^ k [MOD 9] := by
      apply Nat.ModEq.pow
      exact h_k_mod_9
    -- Use periodicity to prove $7 ^ k ≡ 7 ^ 4 (mod 9)$.
    have : 7 ^ k ≡ 7 ^ 4 [MOD 9] := by
      have h_k_mod_3 : k ≡ 1 [MOD 3] := by
        have h_div : 3 ∣ 6 := by norm_num
        have h_eq:  k ≡ 4 [MOD 3] := Nat.ModEq.of_dvd h_div h_k_mod_6
        have h_4_mod_3 : 4 ≡ 1 [MOD 3] := by tauto
        tauto
      have h_7_cycle : 7 ^ 3 ≡ 1 [MOD 9] := by tauto
      have h_7_k : 7 ^ k ≡ 7 ^ (k % 3) [MOD 9] := by
        have : k = (k / 3) * 3 + k % 3 := by rw [mul_comm];exact (Nat.div_add_mod k 3).symm
        conv_lhs => rw [this, pow_add, pow_mul]
        have : 7 ^ (3 * (k / 3)) ≡ 1 [MOD 9] := by
          have : 1 ^ (k / 3) = 1 := by norm_num
          rw [pow_mul, ← this]
          exact Nat.ModEq.pow (k / 3) h_7_cycle
        have : (7 ^ (k / 3)) ^ 3 * 7 ^ (k % 3) ≡ 1 * 7 ^ (k % 3) [MOD 9] := by
          apply Nat.ModEq.mul
          · rw [mul_comm, pow_mul] at this;exact this
          · rfl
        rw [one_mul] at this
        exact this
      have : k % 3 = 1 := by tauto
      rw [this] at h_7_k
      have : 7 ^ 4 ≡ 7 [MOD 9] := by tauto
      exact h_7_k.trans this
    apply Nat.ModEq.trans h_pow_mod_eq
    exact this

  -- Prove that every digit $d ∈ Nat.digits 10 m$ satisfies $d ≤ 9$.
  have h_digits_bound : ∀ m : ℕ, ∀ d ∈ Nat.digits 10 m, d ≤ 9 := by
    intros m d hd
    apply Nat.le_of_lt_succ
    apply Nat.digits_lt_base
    norm_num
    exact hd

  -- Determine the range of $C$
  have h_C_range : C ≤ 13 := by
    have h_D_N_bound : D_N ≤ 111111 := by linarith
    -- Gradually determine the range of $C$ based on the upper bound of the digit sum.
    have h_A_bound : A ≤ 9 * D_N := by
      rw [hA, hD_N]
      have : (Nat.digits 10 N).sum ≤ (Nat.digits 10 N).length * 9 := by
        apply List.sum_le_card_nsmul
        exact h_digits_bound N
      linarith
    have h_A_le : A ≤ 999999 := by
      apply le_trans h_A_bound
      apply mul_le_mul_of_nonneg_left h_D_N_bound
      norm_num
    have h_B_bound : B ≤ 54 := by
      rw [hB]
      have : (Nat.digits 10 A).length ≤ 6 := by
        have : (Nat.digits 10 999999).length = 6 := by norm_num
        rw [← this]
        apply Nat.le_digits_len_le 10 A 999999
        exact h_A_le
      have : (Nat.digits 10 A).sum ≤ (Nat.digits 10 A).length * 9 := by
        apply List.sum_le_card_nsmul
        exact h_digits_bound A
      linarith
    have h_C_bound : C ≤ 13 := by
      rw [hC]
      have : (Nat.digits 10 B).length ≤ 2 := by
        have : (Nat.digits 10 54).length = 2 := by norm_num
        rw [← this]
        apply Nat.le_digits_len_le 10 B 54
        exact h_B_bound
      -- Derive that the digit sum of $B$ is at most $13$ by $B ≤ 54$.
      have : (Nat.digits 10 B).sum ≤ 13 := by
        cases le_or_lt B 9 with
        | inl h_B_le_9 =>
          calc
            (Nat.digits 10 B).sum ≤ B := by
              apply Nat.digit_sum_le
            _ ≤ 9 := by assumption
            _ ≤ 13 := by norm_num
        | inr h_B_gt_9 =>
          have h_B_ne_zero : B ≠ 0 := by linarith
          have h_digits_B : (Nat.digits 10 B) = [B % 10] ++ Nat.digits 10 (B / 10) := by
            apply Nat.digits_eq_cons_digits_div
            norm_num
            exact h_B_ne_zero
          have h_div_ne_zero : B / 10 ≠ 0 := by omega
          have h_div_lt_10 : B / 10 < 10 := by omega
          have h_digits_div : Nat.digits 10 (B / 10) = [B / 10] := by
            apply Nat.digits_of_lt
            exact h_div_ne_zero
            exact h_div_lt_10
          have h_digits_B_eq : (Nat.digits 10 B) = [B % 10, B / 10] := by
            rw [h_digits_B, h_digits_div]
            simp
          have h_mod_le_9 : B % 10 ≤ 9 := by omega
          have h_div_le_5 : B / 10 ≤ 5 := by omega
          have h_sum_le_13 : (B % 10) + (B / 10) ≤ 13 := by
            -- Distinguish cases where $B ≥ 50$ and $B < 50$.
            by_cases h_div_eq_5 : B / 10 = 5
            · have h_B_ge_50 : 50 ≤ B := by omega
              have h_B_le_54 : B ≤ 54 := h_B_bound
              have h_mod_le_4 : B % 10 ≤ 4 := by omega
              calc
                (B % 10) + (B / 10) ≤ 4 + 5 := by
                  apply add_le_add
                  exact h_mod_le_4
                  rw [h_div_eq_5]
                _ = 9 := by norm_num
                _ ≤ 13 := by norm_num
            · have h_div_le_4 : B / 10 ≤ 4 := by omega
              calc
                (B % 10) + (B / 10) ≤ 9 + 4 := by
                  apply add_le_add
                  exact h_mod_le_9
                  exact h_div_le_4
                _ = 13 := by norm_num
          -- The digit sum equals $(B % 10) + (B / 10)$.
          calc
            (Nat.digits 10 B).sum = (B % 10) + (B / 10) := by
              rw [h_digits_B_eq]
              simp [List.sum]
            _ ≤ 9 + 4 := by linarith
            _ = 13 := by norm_num
      linarith
    exact h_C_bound

  -- Verify $C = 7$.
  have h_C_eq_7 : C = 7 := by
    have h_C_mod_9 : C ≡ 7 [MOD 9] := by
      have h_N_ge_C : C ≤ N := by omega
      have h_N_C_mod : N ≡ C [MOD 9] := ((Nat.modEq_iff_dvd' h_N_ge_C).mpr h_N_C).symm
      apply Nat.ModEq.trans h_N_C_mod.symm
      exact h_N_mod_9
    have h_C_range : C ≤ 13 := h_C_range
    have h_C_mod_9_val : C % 9 = 7 := by tauto
    have : C = 7 := by omega
    exact this

  -- Conclusion.
  exact h_C_eq_7
