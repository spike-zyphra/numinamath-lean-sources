import Mathlib

theorem number_theory_278474 (n : ℕ) (h₀ : n ∈ Finset.Icc 10000 99999) (h₁ : 271 ∣ n) :
    ∀ k, k ∈ Finset.Icc 1 5 → 271 ∣ (n / 10 ^ k + (n % 10 ^ k) * 10 ^ (5 - k)) := by
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₃, h₄⟩ 
  intro k hk 
  rw [Finset.mem_Icc] at hk
  rcases hk with ⟨hk1, hk2⟩
  interval_cases k <;> norm_num at *
  <;> omega