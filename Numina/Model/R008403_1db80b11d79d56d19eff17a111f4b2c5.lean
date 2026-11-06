import Mathlib

open Finset

theorem number_theory_7246 {F L : ℕ → ℤ}
    (hF : ∀ n ≥ 2, F n = F (n - 1) + F (n - 2))
    (hL : ∀ n ≥ 2, L n = L (n - 1) + L (n - 2))
    (hF0 : F 0 = 1) (hF1 : F 1 = 1)
    (hL0 : L 0 = 1) (hL1 : L 1 = 3) :
    ∀ n, Int.gcd (F n) (F (n + 1)) = 1 ∧ Int.gcd (L n) (L (n + 1)) = 1 := by
  intro n
  constructor
  · -- (F n).gcd (F (n + 1)) = 1
    obtain ⟨F', hF'⟩ := show ∃ F' : ℕ → ℕ, ∀n, F n = F' n by
      use λn ↦ (F n).natAbs
      intro x
      rw [Eq.comm]
      simp
      induction' x using Nat.strongRec with x ih
      by_cases h₁ : x = 0
      · rw [h₁, hF0]
        simp
      by_cases h₂ : x = 1
      · rw [h₂, hF1]
        simp
      rw [hF]
      linarith [ih (x - 1) (by omega), ih (x - 2) (by omega)]
      omega
    have hF'' : ∀ n ≥ 2, F' n = F' (n - 1) + F' (n - 2) := by
      intro x hx
      specialize hF x hx
      repeat rw [hF'] at hF
      norm_cast at hF
    rw [hF', hF']; simp
    induction' n using Nat.strongRec with n ih
    by_cases h : n = 0
    · have := hF' 0
      rw [hF0, Eq.comm] at this
      simp at this
      rw [h, this]
      simp
    nth_rw 2 [hF'']
    simp
    specialize ih (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, Nat.gcd_comm] at ih
    exact ih
    omega
  · -- (L n).gcd (L (n + 1)) = 1
    obtain ⟨L', hL'⟩ := show ∃ L' : ℕ → ℕ, ∀n, L n = L' n by
      use λn ↦ (L n).natAbs
      intro x
      rw [Eq.comm]
      simp
      induction' x using Nat.strongRec with x ih
      by_cases h₁ : x = 0
      · rw [h₁, hL0]
        simp
      by_cases h₂ : x = 1
      · rw [h₂, hL1]
        simp
      rw [hL]
      linarith [ih (x - 1) (by omega), ih (x - 2) (by omega)]
      omega
    have hL'' : ∀ n ≥ 2, L' n = L' (n - 1) + L' (n - 2) := by
      intro x hx
      specialize hL x hx
      repeat rw [hL'] at hL
      norm_cast at hL
    rw [hL', hL']; simp
    induction' n using Nat.strongRec with n ih
    by_cases h : n = 0
    · have := hL' 0
      rw [hL0, Eq.comm] at this
      simp at this
      rw [h, this]
      simp
    nth_rw 2 [hL'']
    simp
    specialize ih (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, Nat.gcd_comm] at ih
    exact ih
    omega