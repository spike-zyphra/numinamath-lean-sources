import Mathlib

theorem number_theory_188931 {n : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : ∃ k, 2*n+1 = k^2)
    (h₂ : ∃ m, 3*n+1 = m^2) : n = 40 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨k, hk₁⟩
  rcases h₂ with ⟨m, hm₂⟩
  have hk2 : k ≤ 14 := by
    nlinarith [show k ^ 2 ≤ 199 by nlinarith [show n ≤ 99 by linarith, hk₁]]
  have hm2 : m ≤ 17 := by
    nlinarith [show m ^ 2 ≤ 298 by nlinarith [show n ≤ 99 by linarith, hm₂]]
  interval_cases k <;> interval_cases m
  <;> omega