import Mathlib

theorem number_theory_7240 (n : ℕ) (hn : n > 0) :
    ∃ x y z : ℕ, n = x ^ 2 + y ^ 2 - z ^ 2 := by
  by_cases h : n % 2 = 0
  · -- Assume n is even
    have h1 : ∃ k, n = 2 * k := by
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    by_cases h' : k > 1
    · -- Assume k > 1
      use k, 1, k - 1
      cases k with
      | zero =>
        omega -- contradiction because n >0
      | succ k =>
        cases k with
        | zero =>
          omega -- contradiction because k >1
        | succ k =>
          cases k with
          | zero =>
            omega -- contradiction because k >1
          | succ k =>
            simp [Nat.pow_succ, Nat.mul_sub] at *
            all_goals
              ring_nf at *
              all_goals
                omega
    · -- Assume k ≤ 1
      have h1 : k = 0 ∨ k = 1 := by
        omega
      rcases h1 with (r | r)
      · -- k = 0
        rw [r] at hk
        omega -- contradiction
      · -- k = 1
        rw [r] at hk
        use 1, 1, 0
        all_goals
          omega
  · -- Assume n is odd
    have h1 : ∃ k, n = 2 * k + 1 := by
      refine' ⟨(n - 1) / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    by_cases h' : k > 1
    · -- Assume k > 1, then we can set x = k-1, y = 2, z = k-2
      use k - 1, 2, k - 2
      cases k with
      | zero =>
        omega -- contradiction because n >0
      | succ k =>
        cases k with
        | zero =>
          omega -- contradiction because k >1
        | succ k =>
          cases k with
          | zero =>
            omega -- contradiction because k >1
          | succ k =>
            simp [Nat.pow_succ, Nat.mul_sub] at *
            all_goals
              ring_nf at *
              all_goals
                omega
    · -- Assume k ≤ 1, then k = 0 or k = 1
      have h11 : k = 0 ∨ k = 1 := by 
        omega
      rcases h11 with (h11 | h11)
      · -- k = 0, thus n = 1
        rw [show k = 0 by omega] at hk
        have h2 : n = 1 := by 
          omega
        use 1, 0, 0 
        all_goals 
          omega
      · -- k = 1, thus n = 3
        have h2 : n = 3 := by 
          rw [show k = 1 by omega] at hk
          omega
        use 2, 0, 1
        all_goals 
          omega