import Mathlib


open Nat
open Finset


theorem number_theory_127893 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) :
    n = (n / 100 + n % 100) ^ 2 ↔ n = 9801 ∨ n = 3025 ∨ n = 2025 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  constructor
  · -- Forward direction: if n = (n / 100 + n % 100) ^ 2, then n is one of the three numbers
    intro h
    have h5 : n / 100 + n % 100 ≤ 99 := by
      by_contra h6
      push_neg at h6
      have h8 : n / 100 + n % 100 ≥ 100 := by omega
      have h7 : (n / 100 + n % 100) ^ 2 ≥ 10000 := by
        have h8' : n / 100 + n % 100 ≥ 100 := by omega
        have h9 : (n / 100 + n % 100 : ℕ) ≥ 100 := by omega
        have h10 : ((n / 100 + n % 100) : ℕ) ^ 2 ≥ (100 : ℕ) ^ 2 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        nlinarith
      nlinarith
    have h6 : n / 100 + n % 100 ≥ 32 := by
      by_contra h6
      push_neg at h6
      have h7 : (n / 100 + n % 100 : ℕ) ≤ 31 := by omega
      have h8 : (n / 100 + n % 100) ^ 2 ≤ 961 := by
        have h9 : (n / 100 + n % 100 : ℕ) ≤ 31 := by
          omega
        have h10 : ((n / 100 + n % 100) : ℕ) ^ 2 ≤ (31 : ℕ) ^ 2 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals omega
        nlinarith
      nlinarith
    interval_cases k : n / 100 + n % 100 <;> norm_num at h ⊢ <;> omega
  · -- Backward direction: if n = 9801 ∨ n = 3025 ∨ n = 2025, then n = (n / 100 + n % 100) ^ 2
    rintro (rfl | rfl | rfl)
    all_goals norm_num