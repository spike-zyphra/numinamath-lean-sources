import Mathlib

/-What is the smallest positive integer that cannot be written as the sum of two nonnegative palindromic integers? (An integer is palindromic if the sequence of decimal digits are the same when read backwards.)-/

def Is_palindromic (n : ℕ) : Prop := n ≤ 9 ∨ ∃ m: ℕ, n = 11 * m

theorem number_theory_609943: IsLeast {n: ℕ | ¬ ∃ a b: ℕ, Is_palindromic a ∧ Is_palindromic b ∧ n = a + b} 21 := by 
  constructor
  -- Show that 21 is in the set
  · -- Show that 21 cannot be written as the sum of two palindromic numbers
    show ¬ ∃ a b: ℕ, Is_palindromic a ∧ Is_palindromic b ∧ 21 = a + b
    rintro ⟨a, b, h1, h2, h_eq⟩
    have h3 : a ≤ 21 := by omega
    have h4 : b ≤ 21 := by omega
    rcases h1 with h1 | h1
    · -- Case a ≤ 9
      rcases h2 with h2 | h2
      · -- Case b ≤ 9
        interval_cases a <;> interval_cases b <;> omega
      · -- Case b divisible by 11
        rcases h2 with ⟨m, hm⟩
        have hb : b = 11 * m := by omega
        rw [hb] at h_eq
        have hm1 : m ≥ 1 := by omega
        have hm2 : m ≤ 1 := by
          omega
        interval_cases m <;> omega
    · -- Case a divisible by 11
      rcases h1 with ⟨m, hm⟩
      have ha : a = 11 * m := by omega
      rcases h2 with h2 | h2
      · -- Case b ≤ 9
        rw [ha] at h_eq
        have hm1 : m ≥ 1 := by omega
        have hm2 : m ≤ 1 := by 
          omega
        interval_cases m <;> omega
      · -- Case b divisible by 11
        rcases h2 with ⟨k, hk⟩
        have hb : b = 11 * k := by omega
        rw [ha, hb] at h_eq
        have hm1 : m ≥ 1 := by omega
        have hm2 : m ≤ 1 := by
          omega
        have hk1 : k ≥ 1 := by omega
        have hk2 : k ≤ 1 := by
          omega
        interval_cases m <;> interval_cases k <;> omega
  -- Show that any n in the set is ≥ 21
  intro n hn
  show 21 ≤ n
  by_contra h
  push_neg at h
  -- Show that n < 21 implies `n` can be written as sum of two palindromic numbers
  have h6 : n < 21 := by omega
  -- Show that `n < 21` then `n` can be written as the sum of two palindromic numbers
  have h : ∃ a b: ℕ, Is_palindromic a ∧ Is_palindromic b ∧ n = a + b := by
    by_cases h7 : n ≤ 9
    · -- if n ≤ 9
      use n, 0 
      simp [Is_palindromic] at *
      all_goals omega
    · -- 10 ≤ n < 21
      have h8 : n ≥ 10 := by omega
      have h9 : n < 21 := by omega
      by_cases h10 : n = 10
      · -- Case n = 10. Use a = 1, b = 9.
        rw [h10]
        use 1, 9 
        simp [Is_palindromic]
      by_cases h11 : n = 11
      · -- Case n = 11. Use a = 0, b = 11.
        rw [h11]
        use 0, 11 
        simp [Is_palindromic]
      by_cases h12 : n = 12
      · -- Case n = 12. Use a = 1, b = 11.
        rw [h12]
        use 1, 11 
        simp [Is_palindromic]
      by_cases h13 : n = 13
      · -- Case n = 13. Use a = 2, b = 11.
        rw [h13]
        use 2, 11 
        simp [Is_palindromic]
      by_cases h14 : n = 14
      · -- Case n = 14. Use a = 3, b = 11.
        rw [h14]
        use 3, 11 
        simp [Is_palindromic]
      by_cases h15 : n = 15
      · -- Case n = 15. Use a = 4, b = 11.
        rw [h15]
        use 4, 11 
        simp [Is_palindromic]
      by_cases h16 : n = 16
      · -- Case n = 16. Use a = 5, b = 11.
        rw [h16]
        use 5, 11 
        simp [Is_palindromic]
      by_cases h17 : n = 17
      · -- Case n = 17. Use a = 6, b = 11.
        rw [h17]
        use 6, 11 
        simp [Is_palindromic]
      by_cases h18 : n = 18
      · -- Case n = 18. Use a = 7, b = 11.
        rw [h18]
        use 7, 11 
        simp [Is_palindromic]
      by_cases h19 : n = 19
      · -- Case n = 19. Use a = 8, b = 11.
        rw [h19]
        use 8, 11 
        simp [Is_palindromic]
      · -- Case n = 20. Use a = 9, b = 11.
        have h20 : n = 20 := by omega
        rw [h20]
        use 9, 11 
        simp [Is_palindromic]
  -- Now with the existence we can derive a contradiction
  contradiction