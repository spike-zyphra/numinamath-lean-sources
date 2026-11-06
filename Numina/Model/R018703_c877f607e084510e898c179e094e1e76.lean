import Mathlib

theorem number_theory_160307 : IsGreatest {x | ∀ a b c d : ℤ, x ∣ (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d)} 12 := by
  constructor
  · -- Show that 12 is in the set.
    intro a b c d
    have h1 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 4 = 0 := by
      have h4 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by omega
      have h5 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
      have h6 : c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega
      have h7 : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by omega
      rcases h4 with (h4 | h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5 | h5) <;> rcases h6 with (h6 | h6 | h6 | h6) <;> rcases h7 with (h7 | h7 | h7 | h7) <;> 
        simp [Int.mul_emod, Int.sub_emod, h4, h5, h6, h7]
      all_goals omega
    have h2 : (a - b) * (a - c) * (a - d) * (b - c) * (b - d) * (c - d) % 3 = 0 := by
      have h4 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
      have h5 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
      have h6 : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
      have h7 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
      rcases h4 with (h4 | h4 | h4) <;> rcases h5 with (h5 | h5 | h5) <;> rcases h6 with (h6 | h6 | h6) <;> rcases h7 with (h7 | h7 | h7) <;> 
        simp [Int.mul_emod, Int.sub_emod, h4, h5, h6, h7]
      all_goals omega
    omega
  · -- Show that 12 is greatest in the set.
    intro x h
    have h2 := h 1 2 3 4
    norm_num at h2 ⊢
    have h3 : x ∣ 12 := by 
      try exact h2
    have h4 : x ≤ 12 := by 
      apply Int.le_of_dvd (by norm_num) h3
    linarith