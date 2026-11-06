import Mathlib

theorem number_theory_233657 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : ∃ k, n % 100 = k * 11)
    (h₂ : 7 ∣ (Nat.digits 10 n).sum) :
    7 ∈ Nat.primeFactors n := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨k, hk⟩
  interval_cases n <;> norm_num
    [Nat.primeFactors, Nat.primeFactorsList] at *
    <;> try { contradiction }
    <;> omega