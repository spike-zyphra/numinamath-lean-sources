import Mathlib

open Nat

theorem number_theory_129902 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : {k | k ∣ n ∧ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 9 ∨ k = 10 ∨ k = 15 ∨ k = 18 ∨ k = 30}.encard = 8 - 4) :
    n = 36 ∨ n = 45 ∨ n = 72 := by
  have h2 : n ≥ 10 := by
    simp at h₀ ⊢
    omega

  have h3 : n ≤ 99 := by
    simp at h₀ ⊢
    omega
  have h5 : {k | k ∣ n ∧ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 9 ∨ k = 10 ∨ k = 15 ∨ k = 18 ∨ k = 30} = Finset.filter (fun k => k ∣ n ∧ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 9 ∨ k = 10 ∨ k = 15 ∨ k = 18 ∨ k = 30) (Finset.Icc 0 30) := by
    ext k
    simp
    intro h
    rcases h with (⟨h10, hk⟩ | h | h | h | h | h | h | h)
    ·
      have hk3 : k = 3 := hk
      have hk4 : k ≤ 30 := by linarith
      omega
    · 
      have hk4 : k = 4 := by
        omega
      have hk4' : k ≤ 30 := by linarith
      omega
    · 
      have hk5 : k = 5 := by
        omega
      have hk5' : k ≤ 30 := by linarith
      omega
    · 
      have hk9 : k = 9 := by
        omega
      have hk9' : k ≤ 30 := by linarith
      omega
    · 
      have hk10 : k = 10 := by
        omega
      have hk10' : k ≤ 30 := by linarith
      omega
    · 
      have hk15 : k = 15 := by
        omega
      have hk15' : k ≤ 30 := by linarith
      omega
    · 
      have hk18 : k = 18 := by
        omega
      have hk18' : k ≤ 30 := by linarith
      omega
    · 
      have hk30 : k = 30 := by
        omega
      have hk30' : k ≤ 30 := by linarith
      omega
  rw [h5] at h₁
  rw [Set.encard_coe_eq_coe_finsetCard] at h₁
  interval_cases n <;> try { 
    norm_num at h₁ ⊢ 
    all_goals 
      try tauto
  }