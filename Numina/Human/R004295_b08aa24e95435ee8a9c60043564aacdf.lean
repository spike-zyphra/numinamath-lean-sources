import Mathlib

lemma help (m : ℕ) (h : m > 0) : 5^m % 10 = 5 := by
  induction' m, h using Nat.le_induction with m hm hm'
  · simp
  · omega

/- 4B. Among the first 10000 natural numbers, how many end in 1 and can be written in the form $5^{m}+8^{n}$? -/
theorem number_theory_249508 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 1 10000 ∧ x % 10 = 1 ∧ ∃ m n, m > 0 ∧ n > 0 ∧ x = 5^m + 8^n} = 5 := by
      --set S := {x : ℕ | x ∈ Finset.Icc 1 10000 ∧ x % 10 = 1 ∧ ∃ m n, m > 0 ∧ n > 0 ∧ x = 5^m + 8^n}
      --Our goal is to show that S = {4101, 4121, 4221, 4721, 7221}
      have : {x : ℕ | x ∈ Finset.Icc 1 10000 ∧ x % 10 = 1 ∧ ∃ m n, m > 0 ∧ n > 0 ∧ x = 5^m + 8^n} = {4101, 4121, 4221, 4721, 7221} := by
        ext a
        constructor
        intros H
        obtain ⟨h1, h2, h3⟩ := H
        obtain ⟨m, n , hm, hn, h4⟩ := h3
        --Notice that 5^m % 10 = 5
        have H1 : 5^m % 10 = 5 := by
          apply help
          exact hm
        --Therefore, since a % 10 = 1, 8^n % 10 must be 6.
        have H2 : 8^n % 10 = 6 := by
          have H21 : a % 10 = (5^m + 8^n) % 10 := congrFun (congrArg HMod.hMod h4) 10
          rw [Nat.add_mod] at H21
          rw [H1, h2] at H21
          by_contra h
          have cond : 8^n % 10 = 0 ∨ 8^n % 10 = 1 ∨ 8^n % 10 = 2 ∨ 8^n % 10 = 3 ∨ 8^n % 10 = 4 ∨ 8^n % 10 = 5 ∨ 8^n % 10 = 7 := by omega
          rcases cond with H|H|H|H|H|H|H
          all_goals
          rw [H] at H21
          omega

        have H3 : n ≤ 4 := by
          by_contra h
          push_neg at h
          have : 8^n < a := by
            -- Since a = 5^m + 8^n and 5^m > 0, we have 8^n < a
            rw [h4]
            -- 5^m is at least 5 (since m > 0), so 5^m + 8^n > 8^n
            have : 5 ^ m ≥ 5 := by
              cases m with
              | zero => contradiction  -- m > 0, so m cannot be zero
              | succ m => simp [Nat.pow_succ, Nat.mul_comm]; exact Nat.one_le_pow' m 4
            linarith
          have : 8^n ≤ 10000 := by
            have : a ≤ 10000 := by exact (Finset.mem_Icc.mp h1).2
            linarith
          have : n ≥ 5 := by omega
          have : 8^n ≥ 8^5 := by
            apply Nat.pow_le_pow_of_le_right
            · norm_num
            · exact h
          have : 8^5 ≤ 10000 := by linarith
          have : 8^5 > 10000 := by norm_num
          contradiction

        --Now show that n = 4 is the only choice.
        have H4 : n = 4 := by
          by_contra h
          push_neg at h
          interval_cases n
          norm_num at H2
          norm_num at H2
          norm_num at H2
          contradiction

        --Now with n = 4, we find m.
        have H5 : m < 6 := by
          rw [H4] at h4
          ring_nf at h4
          have : a ≤ 10000 := by exact (Finset.mem_Icc.mp h1).2
          rw [h4] at this
          have : 5^m ≤ 5904 := by linarith
          by_contra h
          push_neg at h
          have : 5^6 ≤ 5^m := by
            apply Nat.pow_le_pow_of_le_right
            · norm_num
            · exact h
          have : 5^6 < 5904 := by linarith
          norm_num at this

        have H6 : m ≤ 5 := by omega

        interval_cases m
        rw [H4] at h4
        ring_nf at h4
        simp [h4]
        rw [H4] at h4
        ring_nf at h4
        simp [h4]
        rw [H4] at h4
        ring_nf at h4
        simp [h4]
        rw [H4] at h4
        ring_nf at h4
        simp [h4]
        rw [H4] at h4
        ring_nf at h4
        simp [h4]

        intro H
        rcases H with H1|H2|H3|H4|H5
        simp at *
        constructor
        rw [H1]
        omega
        constructor
        rw [H1]
        use 1
        constructor
        norm_num
        use 4
        constructor
        norm_num
        rw [H1]
        norm_num

        simp at *
        constructor
        rw [H2]
        omega
        constructor
        rw [H2]
        use 2
        constructor
        norm_num
        use 4
        constructor
        norm_num
        rw [H2]
        norm_num

        simp at *
        constructor
        rw [H3]
        omega
        constructor
        rw [H3]
        use 3
        constructor
        norm_num
        use 4
        constructor
        norm_num
        rw [H3]
        norm_num

        simp at *
        constructor
        rw [H4]
        omega
        constructor
        rw [H4]
        use 4
        constructor
        norm_num
        use 4
        constructor
        norm_num
        rw [H4]
        norm_num

        simp at *
        constructor
        rw [H5]
        omega
        constructor
        rw [H5]
        use 5
        constructor
        norm_num
        use 4
        constructor
        norm_num
        rw [H5]
        norm_num
        

      rw [this]
      simp [Set.ncard_eq_toFinset_card']