import Mathlib

theorem number_theory_298149 (x y : ℕ) (hx : x > 0) :
    ∑ i in Finset.Icc 1 x, Nat.factorial i = y ^ 2 ↔ (x = 1 ∧ y = 1) ∨ (x = 3 ∧ y = 3) := by
  constructor
  · -- First, we show that if the equation holds, then (x, y) is either (1, 1) or (3, 3).
    intro h
    by_cases h1 : x ≤ 3
    · -- x ≤ 3, since x > 0, so x = 1, 2, 3
      interval_cases x <;> try { 
        simp [Finset.sum_Icc_succ_top, Nat.factorial] at h 
        all_goals
          have h2 : y ≤ 5 := by nlinarith
          interval_cases y <;> omega 
      }
    · -- x > 3, so x ≥ 4
      have h2 : x ≥ 4 := by linarith
      have h3 : (∑ i in Finset.Icc 1 x, Nat.factorial i) % 5 = 3 := by
        have h4 : ∀ (k : ℕ), k ≥ 4 → (∑ i in Finset.Icc 1 k, Nat.factorial i) % 5 = 3 := by 
          intro k hk
          have base := show (∑ i in Finset.Icc 1 4, Nat.factorial i) % 5 = 3 by 
            native_decide
          have step : ∀ (m : ℕ), m ≥ 4 → (∑ i in Finset.Icc 1 m, Nat.factorial i) % 5 = 3 → (∑ i in Finset.Icc 1 (m + 1), Nat.factorial i) % 5 = 3 := by
            intros m hm h
            have h5 : (∑ i in Finset.Icc 1 (m + 1), Nat.factorial i) = (∑ i in Finset.Icc 1 m, Nat.factorial i) + Nat.factorial (m + 1) := by
              rw [Finset.sum_Icc_succ_top (by linarith)]
            rw [h5]
            rw [Nat.add_mod]
            have h6 : Nat.factorial (m + 1) % 5 = 0 := by
              have h7 : m + 1 ≥ 5 := by linarith
              have h8 : 5 ∣ Nat.factorial (m + 1) := by 
                apply Nat.dvd_factorial
                all_goals linarith
              omega
            omega
          exact Nat.le_induction base step k hk
        specialize h4 x h2
        simpa using h4
      have h4 : y ^ 2 % 5 = 0 ∨ y ^ 2 % 5 = 1 ∨ y ^ 2 % 5 = 4 := by 
        have h1 : y % 5 = 0 ∨ y % 5 = 1 ∨ y % 5 = 2 ∨ y % 5 = 3 ∨ y % 5 = 4 := by omega
        rcases h1 with (h | h | h | h | h) <;> simp [Nat.pow_mod, h]
      have h5 : (∑ i in Finset.Icc 1 x, Nat.factorial i) % 5 = y ^ 2 % 5 := by 
        omega
      omega 
  · -- Backward, if (x, y) is either (1, 1) or (3, 3), then the equation holds
    rintro (h | h)
    · -- x = 1 ∧ y = 1
      rcases h with ⟨rfl, rfl⟩ 
      native_decide 
    · -- x = 3 ∧ y = 3
      rcases h with ⟨rfl, rfl⟩
      native_decide