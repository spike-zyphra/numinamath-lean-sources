import Mathlib

theorem number_theory_275534 (n : ℕ) (h₀ : n ∈ Finset.Icc 10 99) :
    11 ∣ n + (10 * (n % 10) + n / 10) := by
  rw [Finset.mem_Icc] at h₀ 
  rcases h₀ with ⟨h₁₀, h₁₁⟩
  have h2 : n + (10 * (n % 10) + n / 10) = 11 * ((n / 10) + (n % 10)) := by 
    omega
  rw [h2]
  exact ⟨(n / 10) + (n % 10), by ring⟩