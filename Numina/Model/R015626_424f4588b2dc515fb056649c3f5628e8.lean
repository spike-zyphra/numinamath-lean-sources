import Mathlib


theorem number_theory_192355 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) :
    n = 1000 * (n % 10) + 100 * ((n / 10) % 10) +
        10 * ((n / 100) % 10) + (n / 1000) - 8802 ↔ n = 1099 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h1, h2⟩
  constructor
  · -- Proof of the forward direction
    intro h
    have h10 : n + 8802 = 1000 * (n % 10) + 100 * ((n / 10) % 10) + 10 * ((n / 100) % 10) + (n / 1000) := by 
      omega
    have h3 : n ≤ 1197 := by
      have h4 : 1000 * (n % 10) + 100 * ((n / 10) % 10) + 10 * ((n / 100) % 10) + (n / 1000) ≤ 9999 := by
        have h3a : n % 10 ≤ 9 := by omega
        have h3b : (n / 10) % 10 ≤ 9 := by omega
        have h3c : (n / 100) % 10 ≤ 9 := by omega
        have h3d : n / 1000 ≤ 9 := by omega
        omega
      omega
    interval_cases n <;> norm_num at h10 ⊢ 
  · -- Proof of the reverse direction
    intro h
    rw [h]
    all_goals
    norm_num