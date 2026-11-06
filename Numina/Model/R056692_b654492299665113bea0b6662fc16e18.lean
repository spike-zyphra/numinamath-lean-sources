import Mathlib

theorem number_theory_320266 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : n + 3 = 100 * a + 10 * b + c)
    (h₂ : a + b + c = (1 / 3) * (n / 100 + n % 100 / 10 + n % 10)) :
    n = 432 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  omega