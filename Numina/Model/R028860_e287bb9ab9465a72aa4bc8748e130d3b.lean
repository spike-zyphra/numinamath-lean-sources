import Mathlib

theorem number_theory_310392 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : ∑ i in Finset.Icc 1 x, Nat.factorial i = y ^ 2) :
    (x = 1 ∧ y = 1) ∨ (x = 3 ∧ y = 3) := by
  have h1 : x ≥ 1 := by linarith
  have h2 : x ≤ 3 := by
    by_contra h2
    push_neg at h2
    have h3 : x ≥ 4 := by linarith
    have h4 : ∑ i in Finset.Icc 1 x, Nat.factorial i = y ^ 2 := h
    have h5 : x ≥ 4 := by linarith
    have h6 : y ^ 2 % 5 = 0 ∨ y ^ 2 % 5 = 1 ∨ y ^ 2 % 5 = 4 := by
      have h1 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1)
      · simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
      · simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
      · simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
      · simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
      · simp [Nat.pow_mod, h1, Nat.mul_mod, Nat.add_mod]
    have h7 : (∑ i in Finset.Icc 1 x, Nat.factorial i) % 5 = 3 := by
      have h8 : ∀ n, n ≥ 4 → (∑ i in Finset.Icc 1 n, Nat.factorial i) % 5 = 3 := by
        intro n hn
        have base := show (∑ i in Finset.Icc 1 4, Nat.factorial i) % 5 = 3 by
          norm_num [Finset.sum_Icc_succ_top, Nat.factorial]
          <;> omega
        have step : ∀ k, k ≥ 4 → (∑ i in Finset.Icc 1 k, Nat.factorial i) % 5 = 3 → (∑ i in Finset.Icc 1 (k + 1), Nat.factorial i) % 5 = 3 := by
          intro k hk h
          have h9 : (Nat.factorial (k + 1)) % 5 = 0 := by
            have h10 : k + 1 ≥ 5 := by linarith
            have h11 : 5 ∣ Nat.factorial (k + 1) := by
              apply Nat.dvd_factorial
              all_goals linarith
            omega
          have h12 : (∑ i in Finset.Icc 1 (k + 1), Nat.factorial i) = (∑ i in Finset.Icc 1 k, Nat.factorial i) + Nat.factorial (k + 1) := by 
            rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [h12]
          simp [Nat.add_mod, h9, h]
          <;> omega
        exact Nat.le_induction base step n hn
      specialize h8 x (by linarith)
      simpa using h8
    have h8 : (y ^ 2) % 5 = 3 := by
      omega
    omega
  interval_cases x <;> try { 
    norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at h 
    all_goals 
      have : y ≤ 5 := by nlinarith 
      interval_cases y <;> try { simp_all } <;> try { tauto } <;> omega 
    all_goals 
      try { 
        nlinarith 
      }
  }