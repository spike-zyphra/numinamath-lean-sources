import Mathlib

theorem number_theory_231811 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : (n / 1000) % 10 = (n / 100) % 10)
    (h₂ : (n / 10) % 10 = (n % 10)) (h₃ : ∃ k, k^2 = n - 99) :
    n = 1188 ∨ n = 4455 ∨ n = 9900 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₄, h₅⟩
  rcases h₃ with ⟨k, hk⟩
  have hk1 : k ≤ 99 := by
    by_contra h
    push_neg at h
    have : k ^ 2 ≥ 10000 := by 
      have : k ≥ 100 := by linarith
      nlinarith
    have h₇ : n ≤ 9999 := by linarith
    have h₈ : k ^ 2 = n - 99 := by
      omega
    omega
  have hk8 : k ≥ 31 := by
    by_contra h
    push_neg at h
    have : k ≤ 30 := by linarith
    have : k ^ 2 ≤ 900 := by nlinarith
    omega
  interval_cases k <;> norm_num at hk <;> omega