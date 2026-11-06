import Mathlib

theorem inequalities_168755 (a b c d : ℕ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h₁ : a + b + c + d = 192) (h₂ : |(a : ℤ) - b| ≥ 6) (h₃ : |(a : ℤ) - c| ≥ 6)
    (h₄ : |(a : ℤ) - d| ≥ 6) (h₅ : |(b : ℤ) - c| ≥ 6) (h₆ : |(b : ℤ) - d| ≥ 6)
    (h₇ : |(c : ℤ) - d| ≥ 6) :
    min (min a b) (min c d) ≤ 39 := by
  by_contra h
  push_neg at h
  have h8 : min (min a b) (min c d) ≥ 40 := by omega
  have h9 : a ≥ 40 := by
    by_contra h'
    push_neg at h'
    have h10 : min (min a b) (min c d) < 40 := by
      have h11 : a < 40 := by omega
      have h12 : min (min a b) (min c d) ≤ a := by
        have h13 : min (min a b) (min c d) ≤ min a b := by 
          apply min_le_left
        have h14 : min a b ≤ a := by 
          apply min_le_left
        linarith
      omega
    omega
  have h10 : b ≥ 40 := by 
    by_contra h'
    push_neg at h'
    have h11 : min (min a b) (min c d) < 40 := by 
      have h12 : b < 40 := by omega
      have h13 : min (min a b) (min c d) ≤ b := by 
        have h14 : min (min a b) (min c d) ≤ min a b := by 
          apply min_le_left
        have h15 : min a b ≤ b := by 
          apply min_le_right
        linarith
      omega
    omega
  have h11 : c ≥ 40 := by 
    by_contra h'
    push_neg at h'
    have h12 : min (min a b) (min c d) < 40 := by 
      have h13 : c < 40 := by omega
      have h14 : min (min a b) (min c d) ≤ c := by
        have h15 : min (min a b) (min c d) ≤ min c d := by 
          apply min_le_right
        have h16 : min c d ≤ c := by 
          apply min_le_left
        linarith
      omega
    omega
  have h12 : d ≥ 40 := by 
    by_contra h'
    push_neg at h'
    have h13 : min (min a b) (min c d) < 40 := by 
      have h14 : d < 40 := by omega
      have h15 : min (min a b) (min c d) ≤ d := by 
        have h16 : min (min a b) (min c d) ≤ min c d := by 
          apply min_le_right
        have h17 : min c d ≤ d := by 
          apply min_le_right
        linarith
      omega
    omega
  have h13 : a + b + c + d ≥ 160 := by
    omega
  norm_num [abs] at h₂ h₃ h₄ h₅ h₆ h₇
  omega