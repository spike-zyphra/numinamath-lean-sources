import Mathlib

theorem number_theory_225474 : IsGreatest {n | ¬∃ a b c : ℕ , n = 6 * a + 9 * b + 20 * c} 43 := by
  constructor
  · -- Show 43 is in the set.
    intro h
    rcases h with ⟨a, b, c, h_eq⟩
    have h1 : 6 * a + 9 * b + 20 * c = 43 := by
      nlinarith
    have h2 : c ≤ 2 := by
      omega
    have h3 : b ≤ 4 := by
      omega
    have h4 : a ≤ 7 := by 
      omega
    interval_cases c <;> interval_cases b <;> omega
  · -- Show that 43 is greatest in the set.
    intro n hn
    have h : ¬ ∃ a b c : ℕ, n = 6 * a + 9 * b + 20 * c := by
      simpa using hn
    by_contra h1
    push_neg at h1
    -- Now, prove that n > 43 implies n is representable.
    -- This would contradict h.
    have h2 : n > 43 := h1
    have h3 : ∃ a b c : ℕ, n = 6 * a + 9 * b + 20 * c := by
      have h4 : n ≥ 44 := by 
        omega
      have : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases this with (h | h | h | h | h | h)
      · -- n % 6 = 0
        use n / 6, 0, 0
        omega
      · -- n % 6 = 1
        have h6 : n ≥ 49 := by 
          omega
        use (n - 49) / 6, 1, 2
        omega
      · -- n % 6 = 2
        have h6 : n ≥ 20 := by 
          omega
        use (n - 20) / 6, 0, 1
        omega
      · -- n % 6 = 3
        have h6 : n ≥ 9 := by 
          omega
        use (n - 9) / 6, 1, 0
        omega
      · -- n % 6 = 4
        have h6 : n ≥ 40 := by 
          omega
        use (n - 40) / 6, 0, 2
        omega
      · -- n % 6 = 5
        have h6 : n ≥ 29 := by 
          omega
        use (n - 29) / 6, 1, 1
        omega
    contradiction