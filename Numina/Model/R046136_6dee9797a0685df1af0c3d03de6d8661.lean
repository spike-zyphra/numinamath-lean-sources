import Mathlib

theorem number_theory_233386 {n : ℕ} (h₀ : n ∈ Finset.Icc 100 999) (h₁ : ∃ k, n = k * 1111 + 5)
    (h₂ : n % k = 8) :
    n = 665 ∧ k = 73 ∧ n / k = 9 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨k, hk⟩
  by_cases h5 : k > 0
  · -- k > 0, then k ≥ 1.
    have h6 : k ≥ 1 := by omega
    have h7 : n ≥ 1116 := by
      omega
    omega
  · -- k ≤ 0, then k = 0.
    have h8 : k = 0 := by
      omega
    -- substitute k=0 into n = k * 1111 + 5
    -- but this leads to n=5, which contradicts h3: 100 ≤ n
    have h9 : n = 5 := by
      rw [h8] at hk
      omega
    omega