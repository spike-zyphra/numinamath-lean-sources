import Mathlib

theorem number_theory_253761 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) :
    143 ∣ (1000 * n + n) := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₀, h₁⟩
  have h2 : 1000 * n + n = 1001 * n := by
    ring
  rw [h2]
  omega