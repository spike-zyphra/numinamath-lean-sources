import Mathlib

theorem number_theory_233177 (n : ℕ) (h₀ : n ≥ 100) (h₁ : n ≤ 999)
    (h₂ : 7 ∣ n - 7) (h₃ : 8 ∣ n - 8) (h₄ : 9 ∣ n - 9) :
    IsLeast {n | n ≥ 100 ∧ n ≤ 999 ∧ 7 ∣ n - 7 ∧ 8 ∣ n - 8 ∧ 9 ∣ n - 9} 504 := by 
  constructor
  · -- Show that 504 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that 504 is the smallest element in the set
    intro n hn
    rcases hn with ⟨h₀', h₁', h₂', h₃', h₄'⟩
    by_contra h
    push_neg at h
    have h5 : n < 504 := by linarith
    have h6 : n % 7 = 0 := by
      omega
    have h7 : n % 8 = 0 := by
      omega
    have h8 : n % 9 = 0 := by
      omega
    interval_cases n <;> omega