import Mathlib

theorem number_theory_243357
    (a b : ℤ)
    (h₀ : Odd a)
    (h₁ : Odd b)
    (h₂ : |a - b| % 5 = 0) :
    (a^3 - b^3) % 10 = 0 := by
  have h4 : (a - b) % 5 = 0 ∨ (b - a) % 5 = 0 := by 
    cases' abs_cases (a - b) with h h
    · simp [h] at h₂ ⊢; omega
    · simp [h] at h₂ ⊢; omega
  cases h4 with
  | inl h40 =>
    have h5 : a % 5 = b % 5 := by
      omega
    have h9 : a % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h₀
      omega 
    have h10 : b % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h₁
      omega 
    have h11 : a % 10 = b % 10 := by 
      have h6 : a % 5 = b % 5 := h5
      have h7 : a % 2 = 1 := h9
      have h8 : b % 2 = 1 := h10
      omega
    have h12 : a^3 % 10 = b^3 % 10 := by 
      have h90 : a % 10 = b % 10 := h11 
      have h100 : a % 10 = b % 10 := h90 
      have h110 : a^3 % 10 = b^3 % 10 := by 
        have h91 : a % 10 = b % 10 := h100 
        have h92 : a % 10 = b % 10 := h91 
        have : a % 10 = b % 10 := h92 
        have h13 : a % 10 = b % 10 := h92 
        -- Now, we need to show a^3 % 10 = b^3 % 10
        have h14 : a^3 % 10 = b^3 % 10 := by 
          simp [Int.pow_succ, Int.mul_emod, h13] 
          <;> omega 
        exact h14 
      exact h110 
    omega
  | inr h41 =>
    have h5 : a % 5 = b % 5 := by
      omega
    have h9 : a % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h₀
      omega 
    have h10 : b % 2 = 1 := by 
      obtain ⟨k, hk⟩ := h₁
      omega 
    have h11 : a % 10 = b % 10 := by 
      have h6 : a % 5 = b % 5 := h5
      have h7 : a % 2 = 1 := h9
      have h8 : b % 2 = 1 := h10
      omega
    have h12 : a^3 % 10 = b^3 % 10 := by 
      have h90 : a % 10 = b % 10 := h11 
      have h100 : a % 10 = b % 10 := h90 
      have h110 : a^3 % 10 = b^3 % 10 := by 
        have h91 : a % 10 = b % 10 := h100 
        have h92 : a % 10 = b % 10 := h91 
        have : a % 10 = b % 10 := h92 
        have h13 : a % 10 = b % 10 := h92 
        have h14 : a^3 % 10 = b^3 % 10 := by 
          simp [Int.pow_succ, Int.mul_emod, h13] 
          <;> omega 
        exact h14 
      exact h110 
    omega