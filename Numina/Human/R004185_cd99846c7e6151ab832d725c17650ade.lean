import Mathlib

/- A list of length 4 consists of four elements. -/
lemma List_length_four_exists {L : List ℕ} (hL : L.length = 4)
  : ∃ a b c d, L = [a, b, c, d] := by
    -- extract first element
    obtain ⟨a, as, rfl⟩ := List.exists_of_length_succ _ hL

    -- then the rest has length 3
    norm_num at hL
    have as_length : as.length = 3 := by linarith

    -- extract the remaining 3 elements
    obtain ⟨b, c, d, rfl⟩ := List.length_eq_three.mp as_length

    -- then we have four elements
    exists a, b, c, d

/- Problem 3. If the sum of the digits of a four-digit number $X$ is subtracted from $X$, the result is a natural number $N=K^{2}$, where $K$ is a natural number that gives a remainder of 5 when divided by 20 and a remainder of 3 when divided by 21. Find the number $N$. -/
theorem number_theory_241156 (X N K : ℕ) (hX : (Nat.digits 10 X).length = 4) (hN : N = X - (Nat.digits 10 X).sum)
    (hK : N = K^2) (hK1 : K % 20 = 5) (hK2 : K % 21 = 3) : N = 2025 := by
      -- let the four digits be "dcba"
      obtain ⟨a, b, c, d, hh⟩ := List_length_four_exists hX

      -- X is equal to the number formed by the digits "dcba"
      have X_eq := Nat.ofDigits_digits 10 X

      -- so N is equal to a + b * 10 + c * 100 + d * 1000 - (a + b + c + d)
      rw [hh, ←X_eq, hh] at hN
      norm_num [Nat.ofDigits_cons] at hN
      ring_nf at hN

      -- simplifying, N is equal to b * (9 * 1) + c * (9 * 11) + d * (9 * 111)
      have N_eq : N = b * (9 * 1) + c * (9 * 11) + d * (9 * 111) := by omega

      -- so 9 divides N
      have nine_dvd : 9 ∣ N := by
        rw [N_eq]
        apply Nat.dvd_add
        apply Nat.dvd_add
        · exact Dvd.dvd.mul_left (Nat.dvd_mul_right 9 1) b
        · exact Dvd.dvd.mul_left (Nat.dvd_mul_right 9 11) c
        · exact Dvd.dvd.mul_left (Nat.dvd_mul_right 9 111) d

      -- which means that 3 ^ 2 divides K ^ 2
      have sq_dvd : 3 ^ 2 ∣ K ^ 2 := by
        norm_num [←hK]
        tauto

      -- so 3 divides K
      have three_dvd : 3 ∣ K := (Nat.pow_dvd_pow_iff (by omega)).mp sq_dvd

      -- let K = 3 * M
      obtain ⟨M, hM⟩ : ∃ M, K = 3 * M := three_dvd

      -- then M ^ 2 is b * 1 + c * 11 + d * 111
      have M_sq : M ^ 2 = b * 1 + c * 11 + d * 111 := by
        rw [hK, hM] at N_eq
        ring_nf at N_eq
        omega

      have M_sq_le : M ^ 2 < 34 ^ 2 := by
        -- b c and d are less than 10, because they are digits
        have b_mem : b ∈ Nat.digits 10 X := by norm_num [hh]
        have b_lt : b < 10 := Nat.digits_lt_base' b_mem
        have c_mem : c ∈ Nat.digits 10 X := by norm_num [hh]
        have c_lt : c < 10 := Nat.digits_lt_base' c_mem
        have d_mem : d ∈ Nat.digits 10 X := by norm_num [hh]
        have d_lt : d < 10 := Nat.digits_lt_base' d_mem

        -- use bound on digits to get maximum value
        calc M ^ 2
          _ = b * 1 + c * 11 + d * 111 := M_sq
          _ ≤ 9 * 1 + 9 * 11 + 9 * 111 := by gcongr <;> omega
          _ = 1107 := by omega
          -- 34 is next square
          _ < 34 ^ 2 := by norm_num

      -- so M is less than 34
      have ltt := (Nat.pow_lt_pow_iff_left (by omega)).mp M_sq_le

      -- so M is at most 33
      have M_le : M ≤ 33 := by omega

      -- but K = 3 * M, so K is at most 99
      have K_le : K ≤ 99 := by omega

      -- then we can go through the possible values for K manually
      -- we have that K ∈ [0, 99] and x % 20 = 5 and x % 21 = 3
      have K_mem : K ∈ (Finset.Icc 0 99).filter (fun x => x % 20 = 5 ∧ x % 21 = 3) := by
        norm_num
        tauto

      -- but the only possible choice is 45
      have choices : (Finset.Icc 0 99).filter (fun x => x % 20 = 5 ∧ x % 21 = 3) = {45} := by decide

      -- so K is 45
      have K_eq : K = 45 := by
        rw [choices] at K_mem
        aesop
      -- and then N is 45 ^ 2 = 2025
      norm_num [K_eq] at hK
      tauto