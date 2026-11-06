import Mathlib

theorem number_theory_274620 (n : ℕ) (h₀ : n > 0) (h₁ : 91 * 66 * n * 11 = 1000 * n + 10 * n + n) :
    n = 1 := by
  have eq1 : 91 * 66 * n * 11 = 1011 * n := by
    ring_nf at h₁ ⊢
    omega
  have eq2 : 65055 * n = 0 := by
    omega
  have eq3 : n = 0 := by
    omega
  linarith [eq3, h₀]