import Mathlib

theorem number_theory_303908 : IsGreatest {n | ¬∃ k l m : ℕ, n = 6*k + 9*l + 20*m} 43 := by
  constructor
  · -- Show that 43 is in the set.
    intro h
    rcases h with ⟨k, l, m, h_eq⟩
    omega
  · -- Show that any n in the set is ≤ 43
    intro n hn
    by_contra h
    push_neg at h
    have h1 : ∃ k l m : ℕ, n = 6*k + 9*l + 20*m := by
      have h2 : n > 43 := h
      have h3 : n ≥ 44 := by omega
      have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h4 with (h4 | h4 | h4)
      · -- Case n % 3 = 0
        have h5 : n % 3 = 0 := h4
        have h11 : ∃ k l m : ℕ, n = 6*k + 9*l + 20*m := by
          have h6 : n % 3 = 0 := h5
          have h7 : n ≥ 44 := by omega
          have h8 : n % 3 = 0 := h6
          have h9 : ∃ k l : ℕ, 2 * k + 3 * l = n / 3 := by
            have h10 : n % 3 = 0 := h6
            have h11 : n / 3 ≥ 15 := by
              omega
            have h12 : (n / 3) ≥ 15 := h11
            by_cases h13 : (n / 3) % 2 = 0
            · 
              use (n / 3) / 2, 0
              omega
            · 
              use (n / 3 - 3) / 2, 1
              omega
          rcases h9 with ⟨k, l, h14⟩
          use k, l, 0
          omega
        exact h11
      · -- Case n % 3 = 1
        have h5 : n % 3 = 1 := h4
        have h11 : ∃ k l m : ℕ, n = 6*k + 9*l + 20*m := by
          have h6 : n % 3 = 1 := h5
          have h7 : n ≥ 44 := by omega
          have h8 : n % 3 = 1 := h6
          have h9 : ∃ k l : ℕ, 2 * k + 3 * l = (n - 40) / 3 := by
            have h12 : (n - 40) % 3 = 0 := by
              omega
            have h13 : (n - 40) / 3 ≥ 2 := by 
              omega
            by_cases h14 : (n - 40) / 3 % 2 = 0
            · 
              use ((n - 40) / 3) / 2, 0
              omega
            · 
              use ((n - 40) / 3 - 3) / 2, 1
              omega
          rcases h9 with ⟨k, l, h15⟩
          use k, l, 2
          omega
        exact h11
      · -- Case n % 3 = 2
        have h5 : n % 3 = 2 := h4
        have h11 : ∃ k l m : ℕ, n = 6*k + 9*l + 20*m := by
          have h6 : n % 3 = 2 := h5
          have h7 : n ≥ 44 := by omega
          have h8 : n % 3 = 2 := h6
          have h9 : ∃ k l : ℕ, 2 * k + 3 * l = (n - 20) / 3 := by
            have h12 : (n - 20) % 3 = 0 := by
              omega
            have h13 : (n - 20) / 3 ≥ 8 := by 
              omega
            by_cases h14 : (n - 20) / 3 % 2 = 0
            · 
              use ((n - 20) / 3) / 2, 0
              omega
            · 
              use ((n - 20) / 3 - 3) / 2, 1
              omega
          rcases h9 with ⟨k, l, h16⟩
          use k, l, 1
          omega
        exact h11
    have h3 : ¬∃ k l m : ℕ, n = 6*k + 9*l + 20*m := by
      simpa using hn
    contradiction