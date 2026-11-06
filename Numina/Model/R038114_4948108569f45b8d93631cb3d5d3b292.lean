import Mathlib

theorem number_theory_101609 (n : ℕ) (h₀ : n > 100) :
    ∃ a b c, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ a > 1 ∧ b > 1 ∧ c > 1 ∧
      (a * b * c = n + (n + 1) + (n + 2)) ∨
      (a * b * c = n + (n + 1) + (n + 3)) ∨
      (a * b * c = n + (n + 2) + (n + 3)) ∨
      (a * b * c = (n + 1) + (n + 2) + (n + 3))
  := by 
  by_cases h3 : (n + 1) % 2 = 0 
  · -- n+1 is even 
    have h33 : n % 2 = 1 := by 
      omega
    have h31 : ∃ k, n + 1 = 2 * k := by 
      refine' ⟨(n + 1) / 2, by omega⟩ 
    rcases h31 with ⟨k, hk⟩ 
    use 2, 3, k 
    have h32 : k > 50 := by 
      omega 
    have h41 : k > 1 := by 
      omega 
    have h42 : 2 > 1 := by norm_num 
    have h43 : 3 > 1 := by norm_num 
    have ha1 : 2 ≠ 3 := by norm_num 
    have ha2 : 3 ≠ k := by 
      by_contra h 
      have h1 : k = 3 := by 
        omega 
      have h2 : n + 1 = 2 * 3 := by 
        rw [show k = 3 by omega] at hk 
        all_goals linarith 
      omega 
    have ha3 : k ≠ 2 := by 
      by_contra h 
      have h1 : k = 2 := by 
        omega 
      have h2 : n + 1 = 2 * 2 := by 
        rw [show k = 2 by omega] at hk 
        all_goals linarith 
      omega 
    simp [show k > 0 by omega, ha1, ha2, ha3, h41, h42, h43] at *
    all_goals 
      -- Now to consider which disjunction holds 
      have h15 : 2 * 3 * k = n + (n + 1) + (n + 2) := by 
        have h1 : n + 1 = 2 * k := by linarith [hk]
        omega 
      simp [h15] 
  · -- n+1 is odd 
    have h33 : n % 2 = 0 := by 
      omega 
    have h31 : ∃ k, n + 2 = 2 * k := by 
      refine' ⟨(n + 2) / 2, by omega⟩ 
    rcases h31 with ⟨k, hk⟩ 
    use 2, 3, k 
    have h32 : k > 50 := by 
      omega 
    have h41 : k > 1 := by 
      omega 
    have h42 : 2 > 1 := by norm_num 
    have h43 : 3 > 1 := by norm_num 
    have ha1 : 2 ≠ 3 := by norm_num 
    have ha2 : 3 ≠ k := by 
      by_contra h 
      have h1 : k = 3 := by 
        omega 
      have h2 : n + 2 = 2 * 3 := by 
        rw [show k = 3 by omega] at hk 
        all_goals linarith 
      omega 
    have ha3 : k ≠ 2 := by 
      by_contra h 
      have h1 : k = 2 := by 
        omega 
      have h2 : n + 2 = 2 * 2 := by 
        rw [show k = 2 by omega] at hk 
        all_goals linarith 
      omega 
    simp [show k > 0 by omega, ha1, ha2, ha3, h41, h42, h43] at *
    all_goals 
      -- Now to consider which disjunction holds 
      have h15 : 2 * 3 * k = (n + 1) + (n + 2) + (n + 3) := by 
        have h1 : n + 2 = 2 * k := by linarith [hk]
        omega 
      simp [h15]