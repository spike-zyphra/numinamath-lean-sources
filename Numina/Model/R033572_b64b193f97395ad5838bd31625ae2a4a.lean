import Mathlib

theorem number_theory_83622 (n : ℕ) (h₀ : 0 < n) (h₁ : ∃ k, k ∈ Finset.Icc 1000 9999 ∧ k = 12 * n ^ 2 + 12 * n + 11 ∧ (Nat.digits 10 k).length = 4 ∧ (Nat.digits 10 k).toFinset.card = 1) :
    n = 21 := by
  rcases h₁ with ⟨k, hk₁, hk₂, hk₃, hk₄⟩
  rw [Finset.mem_Icc] at hk₁
  rcases hk₁ with ⟨hk₅, hk₆⟩
  have h2 : n ≤ 31 := by
    nlinarith [show 12 * n ^ 2 + 12 * n + 11 ≤ 9999 by nlinarith [hk₂, hk₆], show 12 * n ^ 2 + 12 * n + 11 ≥ 1000 by nlinarith [hk₂, hk₅]]
  interval_cases n <;> norm_num [hk₂] at *
  <;> omega