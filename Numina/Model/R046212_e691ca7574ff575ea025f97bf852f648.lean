import Mathlib

theorem number_theory_221068 (f : ℕ → ℕ) (h₀ : ∀ n, f n ∈ Finset.Icc 1 2023)
    (h₁ : ∀ n, f n % 3 ≠ f (n + 1) % 3) (h₂ : ∀ n, f n % 3 ≠ f (n + 2) % 3)
    (h₃ : ∀ n, f (n + 1) % 3 ≠ f (n + 2) % 3) :
    ∃ n, f n % 3 = 1 := by
  by_contra h
  push_neg at h
  have h10 : f 0 % 3 = 0 ∨ f 0 % 3 = 2 := by
    have h11 : f 0 % 3 < 3 := by
      omega
    have h12 : f 0 % 3 ≥ 0 := by 
      omega 
    have h13 : f 0 % 3 ≠ 1 := h 0
    omega 
  have h11 : f 1 % 3 = 0 ∨ f 1 % 3 = 2 := by
    have h11 : f 1 % 3 < 3 := by
      omega 
    have h12 : f 1 % 3 ≥ 0 := by
      omega 
    have h13 : f 1 % 3 ≠ 1 := h 1 
    omega 
  have h12 : f 2 % 3 = 0 ∨ f 2 % 3 = 2 := by
    have h11 : f 2 % 3 < 3 := by
      omega 
    have h12 : f 2 % 3 ≥ 0 := by
      omega 
    have h13 : f 2 % 3 ≠ 1 := h 2 
    omega 
  have h4 : f 0 % 3 ≠ f 1 % 3 := h₁ 0
  have h5 : f 0 % 3 ≠ f 2 % 3 := h₂ 0 
  have h6 : f 1 % 3 ≠ f 2 % 3 := h₃ 0 
  rcases h10 with (h10 | h10) <;> rcases h11 with (h11 | h11) <;> rcases h12 with (h12 | h12) <;> 
    try { 
      omega 
    }