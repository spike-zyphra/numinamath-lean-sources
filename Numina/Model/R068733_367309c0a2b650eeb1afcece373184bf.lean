import Mathlib

theorem algebra_276621 (a b c d : ℕ) (h₀ : a ≤ 100) (h₁ : b ≤ 100)
    (h₂ : c ≤ 100) (h₃ : d ≤ 100) (h₄ : (a + b + c + d) / 4 = 88) :
    min (min a b) (min c d) ≥ 52 := by 
  have h5 : a + b + c + d ≥ 352 := by 
    omega
  by_contra h
  push_neg at h
  have h6 : a < 52 ∨ b < 52 ∨ c < 52 ∨ d < 52 := by
    by_contra h7
    push_neg at h7
    have h8 : min (min a b) (min c d) ≥ 52 := by
      have h9 : min a b ≥ 52 := by 
        cases min_cases a b with
        | inl h10 =>
          omega
        | inr h11 =>
          omega
      have h10 : min c d ≥ 52 := by 
        cases min_cases c d with
        | inl h12 =>
          omega
        | inr h13 =>
          omega
      cases min_cases (min a b) (min c d) with
      | inl h12 =>
        omega
      | inr h13 =>
        omega
    linarith
  rcases h6 with (h6 | h6 | h6 | h6)
  · -- Case where a < 52
    have h7 : a ≤ 51 := by omega
    have h8 : a + b + c + d ≤ 351 := by 
      omega
    omega
  · -- Case where b < 52
    have h7 : b ≤ 51 := by omega
    have h8 : a + b + c + d ≤ 351 := by 
      omega
    omega
  · -- Case where c < 52
    have h7 : c ≤ 51 := by omega
    have h8 : a + b + c + d ≤ 351 := by 
      omega
    omega
  · -- Case where d < 52
    have h7 : d ≤ 51 := by omega
    have h8 : a + b + c + d ≤ 351 := by 
      omega
    omega