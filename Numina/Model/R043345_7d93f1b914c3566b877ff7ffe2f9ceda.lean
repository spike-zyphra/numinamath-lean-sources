import Mathlib

theorem number_theory_115623 :
    IsLeast {x | ∃ a b c : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a^2 + b^2 - c = 2022 ∧ a^2 + b^2 + c^2 = x} 2034 := by
  constructor 
  · -- Show 2034 is in the set.
    use 36, 27, 3
    all_goals norm_num
  · -- Show no smaller element is in the set.
    rintro x ⟨a, b, c, ha, hb, hc, h1, h2⟩ 
    by_contra h 
    push_neg at h 
    have h3 : c = 1 ∨ c = 2 := by
      have h4 : a ^ 2 + b ^ 2 = c + 2022 := by 
        omega
      have h5 : x = (a ^ 2 + b ^ 2) + c ^ 2 := by 
        linarith
      rw [h4] at h5 
      have h6 : x = (c + 2022) + c ^ 2 := by 
        linarith
      have h7 : (c + 2022) + c ^ 2 < 2034 := by
        linarith [h6, h]
      have h8 : c ≤ 2 := by 
        nlinarith 
      have h40 : c > 0 := by 
        by_contra h'
        push_neg at h'
        have : c = 0 := by linarith 
        tauto 
      have h9 : c = 1 ∨ c = 2 := by 
        interval_cases c <;> omega 
      tauto 
    rcases h3 with (h_eq | h_eq)
    · -- c = 1
      have h5 : a ^ 2 + b ^ 2 = 2023 := by 
        omega 
      have h6 : a ≤ 44 := by nlinarith 
      have h7 : b ≤ 44 := by nlinarith 
      have h8 : (a : ℕ) ^ 2 % 8 = 0 ∨ (a : ℕ) ^ 2 % 8 = 1 ∨ (a : ℕ) ^ 2 % 8 = 4 := by 
        have h1 : (a : ℕ) % 8 = 0 ∨ (a : ℕ) % 8 = 1 ∨ (a : ℕ) % 8 = 2 ∨ (a : ℕ) % 8 = 3 ∨ (a : ℕ) % 8 = 4 ∨ (a : ℕ) % 8 = 5 ∨ (a : ℕ) % 8 = 6 ∨ (a : ℕ) % 8 = 7 := by 
          omega 
        rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h] 
      have h9 : (b : ℕ) ^ 2 % 8 = 0 ∨ (b : ℕ) ^ 2 % 8 = 1 ∨ (b : ℕ) ^ 2 % 8 = 4 := by 
        have h1 : (b : ℕ) % 8 = 0 ∨ (b : ℕ) % 8 = 1 ∨ (b : ℕ) % 8 = 2 ∨ (b : ℕ) % 8 = 3 ∨ (b : ℕ) % 8 = 4 ∨ (b : ℕ) % 8 = 5 ∨ (b : ℕ) % 8 = 6 ∨ (b : ℕ) % 8 = 7 := by 
          omega 
        rcases h1 with (h | h | h | h | h | h | h | h) <;> simp [pow_two, Nat.mul_mod, h] 
      have h10 : (a ^ 2 + b ^ 2) % 8 = 7 := by 
        omega 
      omega 
    · -- c = 2
      have h5 : a ^ 2 + b ^ 2 = 2024 := by 
        omega 
      have h6 : a ≤ 44 := by nlinarith 
      have h7 : b ≤ 44 := by nlinarith 
      interval_cases a <;> try { 
        omega 
      }
      <;> interval_cases b 
      <;> omega