import Mathlib

theorem number_theory_315934 :
    (∀ n : ℕ, 0 < n → ¬ 5 ∣ 3^n + 2 * 17^n) ∧
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3^n + 2 * 17^n} 4 := by 
  constructor 
  · -- Prove: For any positive integer n, 3^n + 2 × 17^n is not a multiple of 5 
    intro n hn
    have h1 : (3^n + 2 * 17^n) % 5 = 2 ∨ (3^n + 2 * 17^n) % 5 = 3 := by
      have h2 : ∀ n : ℕ, (3^n + 2 * 17^n) % 5 = 2 ∨ (3^n + 2 * 17^n) % 5 = 3 := by
        intro n 
        induction' n using Nat.strongRecOn with n ih 
        cases n with 
        | zero => 
          simp 
        | succ n => 
          cases n with 
          | zero => 
            norm_num 
          | succ n => 
            have h3 := ih (n) (by omega) 
            simp [Nat.pow_succ, show 17 % 5 = 2 by norm_num, show 3 % 5 = 3 by norm_num] at h3 ⊢ 
            omega 
      specialize h2 n 
      simpa using h2
    have h2 : ¬ 5 ∣ 3 ^ n + 2 * 17 ^ n := by 
      have h3 : (3 ^ n + 2 * 17 ^ n) % 5 = 2 ∨ (3 ^ n + 2 * 17 ^ n) % 5 = 3 := h1 
      omega 
    exact h2
  · -- Prove: 4 is the least positive integer that satisfies $3^n + 2 \cdot 17^n$ divisible by 11.
    constructor
    · -- Show 4 is in the set.
      constructor
      · -- Show 4 is positive.
        norm_num 
      · -- Show 11 divides $3^4 + 2 \cdot 17^4$.
        norm_num 
    · -- Show 4 is the least.
      intro n hn
      rcases hn with ⟨hn_pos, hn_div⟩ 
      by_contra h 
      push_neg at h 
      have h6 : n < 4 := by linarith 
      interval_cases n <;> norm_num at hn_div