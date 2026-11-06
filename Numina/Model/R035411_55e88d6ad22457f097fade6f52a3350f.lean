import Mathlib

theorem number_theory_315439 (x y : ℕ) (hx : x > 0) (hy : y > 0)
    (h : ∑ i in Finset.Icc 1 x, Nat.factorial i = y ^ 2) :
    (x = 1 ∧ y = 1) ∨ (x = 3 ∧ y = 3) := by
  have h1 : x ≥ 1 := by linarith
  by_cases h2 : x ≤ 3
  · -- If x ≤ 3, x is 1, 2 or 3
    have h3 : x ≤ 3 := h2
    have h4 : x = 1 ∨ x = 2 ∨ x = 3 := by
      omega
    rcases h4 with (h4 | h4 | h4)
    · -- x = 1
      rw [h4] at h
      norm_num [Finset.sum_Icc_succ_top] at h
      have h5 : y ≤ 1 := by nlinarith
      have h6 : y = 1 := by nlinarith
      left
      constructor
      · -- x = 1
        linarith
      · -- y = 1
        linarith
    · -- x = 2
      rw [h4] at h
      norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at h
      all_goals
      have h7 : y ≤ 2 := by nlinarith
      interval_cases y <;> omega
    · -- x = 3
      rw [h4] at h
      norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at h
      have h8 : y ≤ 3 := by nlinarith
      have h9 : y = 3 := by nlinarith
      right
      constructor
      · -- x = 3
        linarith
      · -- y = 3
        linarith
  · -- x > 3, so x >= 4
    have h4 : x ≥ 4 := by omega
    by_cases h5 : x ≤ 4
    · -- x = 4
      have h6 : x = 4 := by omega
      rw [h6] at h
      norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at h
      all_goals
      have h8 : y ≤ 5 := by nlinarith
      interval_cases y <;> omega
    · -- x ≥ 5
      have h6 : x ≥ 5 := by omega
      have h7 : y ^ 2 % 5 = 0 ∨ y ^ 2 % 5 = 1 ∨ y ^ 2 % 5 = 4 := by
        have h8 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by
          omega
        rcases h8 with (h8 | h8 | h8 | h8 | h8)
        · -- y % 5 = 0
          simp [Nat.pow_mod, h8, Nat.mul_mod, Nat.add_mod]
        · -- y % 5 = 1
          simp [Nat.pow_mod, h8, Nat.mul_mod, Nat.add_mod]
        · -- y % 5 = 2
          simp [Nat.pow_mod, h8, Nat.mul_mod, Nat.add_mod]
        · -- y % 5 = 3
          simp [Nat.pow_mod, h8, Nat.mul_mod, Nat.add_mod]
        · -- y % 5 = 4
          simp [Nat.pow_mod, h8, Nat.mul_mod, Nat.add_mod]
      have h8 : (∑ i in Finset.Icc 1 x, Nat.factorial i) % 5 = 3 := by
        have h9 : ∀ (n : ℕ), n ≥ 5 → (∑ i in Finset.Icc 1 n, Nat.factorial i) % 5 = 3 := by
          intro n hn
          have base5 : (∑ i in Finset.Icc 1 5, Nat.factorial i) % 5 = 3 := by
            native_decide
          have step5 : ∀ (k : ℕ), k ≥ 5 → (∑ i in Finset.Icc 1 k, Nat.factorial i) % 5 = 3 →
            (∑ i in Finset.Icc 1 (k + 1), Nat.factorial i) % 5 = 3 := by
            intro k hk h
            have h12 : ∑ i in Finset.Icc 1 (k + 1), Nat.factorial i = (∑ i in Finset.Icc 1 k, Nat.factorial i) + Nat.factorial (k + 1) := by
              rw [Finset.sum_Icc_succ_top (by omega)]
              <;> try { rfl }
              all_goals
                try { linarith }
            rw [h12]
            simp [Nat.add_mod, h]
            have h11 : Nat.factorial (k + 1) % 5 = 0 := by
              have h11 : k + 1 ≥ 5 := by omega
              have h15 : 5 ∣ Nat.factorial (k + 1) := by
                apply Nat.dvd_factorial
                all_goals linarith
              omega
            all_goals omega
          exact Nat.le_induction base5 step5 n hn
        specialize h9 x h6
        linarith [h9]
      have h9 : y ^ 2 % 5 = 3 := by 
        omega
      omega