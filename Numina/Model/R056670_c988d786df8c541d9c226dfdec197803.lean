import Mathlib

theorem number_theory_114667 (n : ℕ) (h : n ∈ Finset.Icc 100 999) :
    n = 11 * (Nat.digits 10 n).sum ↔ n = 198 := by
  rw [Finset.mem_Icc] at h
  rcases h with ⟨h1, h2⟩
  constructor
  · -- Forward direction: if n = 11 * (Nat.digits 10 n).sum, then n = 198
    intro h_eq
    interval_cases n <;> norm_num at h_eq ⊢
      <;> norm_num [Nat.digits, Nat.digitsAux] at h_eq ⊢
      <;> omega
  · -- Backward direction: if n = 198, then n = 11 * (Nat.digits 10 n).sum
    intro h_eq
    rw [h_eq]
    norm_num