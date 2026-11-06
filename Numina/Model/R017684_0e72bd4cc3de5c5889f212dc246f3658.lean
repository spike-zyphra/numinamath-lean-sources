import Mathlib

theorem number_theory_165324 (f : ℕ → ℕ) :
    (∀ n, f (2 * n) = 2 * f n) ∧ (∀ n, f (2 * n + 1) = 2 * f n + 1) ↔
    ∀ n, f n = n := by 
  constructor
  · -- Assume the recurrence relations hold, prove f(n) = n
    intro h
    rcases h with ⟨h1, h2⟩
    intro n
    have h3 : ∀ n, f n = n := by 
      intro n 
      induction' n using Nat.strongRecOn with n ih 
      cases n with
      | zero =>
        have h4 : f 0 = 0 := by
          have h5 : f (2 * 0) = 2 * f 0 := h1 0
          simp at h5 
          omega 
        exact h4 
      | succ n => 
        by_cases h5 : (n + 1) % 2 = 0 
        · -- n + 1 is even 
          have h6 : (n + 1) % 2 = 0 := h5 
          have h7 : ∃ m, n + 1 = 2 * m := by 
            refine' ⟨(n + 1) / 2, by omega⟩ 
          rcases h7 with ⟨m, hm⟩ 
          have h8 : m < n + 1 := by 
            omega 
          have h9 : f m = m := by 
            apply ih 
            all_goals 
              omega 
          calc 
            f (n + 1) = f (2 * m) := by rw [hm] 
            _ = 2 * f m := by 
              apply h1 
            _ = 2 * m := by 
              rw [h9] 
            _ = n + 1 := by 
              omega 
        · -- n + 1 is odd 
          have h6 : (n + 1) % 2 = 1 := by 
            omega 
          have h7 : ∃ m, n + 1 = 2 * m + 1 := by 
            refine' ⟨(n + 1 - 1) / 2, by omega⟩ 
          rcases h7 with ⟨m, hm⟩ 
          have h8 : m < n + 1 := by 
            omega 
          have h9 : f m = m := by 
            apply ih 
            all_goals 
              omega 
          calc 
            f (n + 1) = f (2 * m + 1) := by 
              rw [hm] 
            _ = 2 * f m + 1 := by 
              apply h2 
            _ = 2 * m + 1 := by 
              rw [h9] 
            _ = n + 1 := by 
              omega 
    exact h3 n 
  · -- Assume f(n) = n, prove the recurrence relations
    intro h 
    constructor 
    · -- Show that ∀ n, f (2 * n) = 2 * f n 
      intro n 
      have h1 : f (2 * n) = 2 * n := by 
        apply h (2 * n) 
      have h2 : f n = n := by 
        apply h n 
      omega 
    · -- Show that ∀ n, f (2 * n + 1) = 2 * f n + 1 
      intro n 
      have h1 : f (2 * n + 1) = 2 * n + 1 := by 
        apply h (2 * n + 1) 
      have h2 : f n = n := by 
        apply h n 
      omega