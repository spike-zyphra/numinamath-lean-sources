import Mathlib

theorem number_theory_289739 (n : ℕ) (h₀ : n^2 < (n + 1)^2) (h₁ : (n + 1)^2 - n^2 = 89) :
    n^2 = 1936 := by
  have eq1 : (n + 1 : ℕ)^2 = n^2 + 2 * n + 1 := by
    ring
  have eq2 : (n + 1)^2 - n^2 = 2 * n + 1 := by
    rw [eq1]
    omega
  rw [eq2] at h₁
  have h₂ : 2 * n + 1 = 89 := h₁
  have h₃ : 2 * n = 88 := by
    omega
  have h₄ : n = 44 := by
    omega
  calc
    n^2 = 44^2 := by rw [h₄]
    _ = 1936 := by norm_num