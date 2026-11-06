import Mathlib

theorem number_theory_17133 (s c : ℕ+) (hs : IsLeast {n : ℕ+ | 20 ∣ n.val ∧ IsSquare n.val} s)
    (hc : IsLeast {n : ℕ+ | 20 ∣ n.val ∧ ∃ k, n.val = k ^ 3} c) :
    ((Finset.Icc s.val c.val).filter fun n => 20 ∣ n).card = 46 := by
  have h1 : s.val = 100 := by
    have h2 : s ∈ {n : ℕ+ | 20 ∣ n.val ∧ IsSquare n.val} := by
      exact hs.1
    have h3 : ∀ n : ℕ+, n ∈ {n : ℕ+ | 20 ∣ n.val ∧ IsSquare n.val} → s.val ≤ n.val := by
      apply hs.2
    have h4 : s.val ≤ 100 := by
      have h5 : (100 : ℕ+) ∈ {n : ℕ+ | 20 ∣ n.val ∧ IsSquare n.val} := by
        constructor
        · -- show that 20 divides 100
          norm_num
        · -- show that 100 is square
          native_decide
      have h6 : s.val ≤ (100 : ℕ+).val := by
        apply h3 (100)
        exact h5
      have h7 : s.val ≤ 100 := by
        exact_mod_cast h6
      linarith
    have h8 : 100 ≤ s.val := by
      have h9 : s ∈ {n : ℕ+ | 20 ∣ n.val ∧ IsSquare n.val} := by 
        exact hs.1
      rcases h9 with ⟨h20, hsq⟩
      by_contra h
      push_neg at h
      have h10 : s.val < 100 := by
        exact_mod_cast h
      rcases hsq with ⟨r, hr⟩
      have h20' : s.val % 20 = 0 := by 
        have h : 20 ∣ s.val := h20
        omega
      have h13 : r ≤ 9 := by
        nlinarith [hr]
      interval_cases r <;> norm_num at hr
      all_goals
        norm_num [hr] at h20' <;> omega
    exact Nat.le_antisymm h4 h8
  have h2 : c.val = 1000 := by
    have h3 : c ∈ {n : ℕ+ | 20 ∣ n.val ∧ ∃ k, n.val = k ^ 3} := by
      exact hc.1
    have h4 : ∀ n : ℕ+, n ∈ {n : ℕ+ | 20 ∣ n.val ∧ ∃ k, n.val = k ^ 3} → c.val ≤ n.val := by 
      apply hc.2
    have h5 : c.val ≤ 1000 := by
      have h6 : (1000 : ℕ+) ∈ {n : ℕ+ | 20 ∣ n.val ∧ ∃ k, n.val = k ^ 3} := by 
        constructor
        · -- Show 20 divides 1000
          norm_num
        · -- Show exists k, 1000 = k^3
          use 10
          all_goals norm_num
      have h7 : c.val ≤ (1000 : ℕ+).val := by 
        apply h4 1000
        exact h6
      have h8 : c.val ≤ 1000 := by
        exact_mod_cast h7
      linarith
    have h9 : 1000 ≤ c.val := by
      have h10 : c ∈ {n : ℕ+ | 20 ∣ n.val ∧ ∃ k, n.val = k ^ 3} := by
        exact hc.1
      rcases h10 with ⟨h20, k, hk⟩
      by_contra h
      push_neg at h
      have h11 : c.val < 1000 := by
        exact_mod_cast h
      have h12 : k < 10 := by 
        by_contra h13
        push_neg at h13
        have h14 : k ^ 3 ≥ 1000 := by
          have h14k : k ≥ 10 := by
            omega
          have h15k : k ^ 3 ≥ 1000 := by
            have hk : k ≥ 10 := h14k
            have h20 : k ^ 3 ≥ 1000 := by
              have hk : k ≥ 10 := by omega
              have h2 : k ≥ 10 := by omega
              have h4 : k ^ 3 ≥ 10 ^ 3 := by 
                apply Nat.pow_le_pow_left
                all_goals omega
              norm_num at h4 ⊢
              linarith
            linarith
          linarith
        omega
      interval_cases k <;> norm_num at hk
      all_goals
        norm_num [hk] at h20 <;> omega
    exact Nat.le_antisymm h5 h9
  rw [h1, h2]
  native_decide