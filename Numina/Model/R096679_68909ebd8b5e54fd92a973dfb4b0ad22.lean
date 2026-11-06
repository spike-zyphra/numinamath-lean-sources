import Mathlib

theorem number_theory_206440 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    n = 12 * (Nat.digits 10 n).sum ↔ n = 108 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₁, h₂⟩
  constructor
  · -- Forward direction: if n = 12 * sum of digits, then n = 108
    intro h
    interval_cases n <;> norm_num at h ⊢ <;> omega
  · -- Backward direction: if n = 108, then n = 12 * sum of digits
    intro h
    rw [h]
    norm_num