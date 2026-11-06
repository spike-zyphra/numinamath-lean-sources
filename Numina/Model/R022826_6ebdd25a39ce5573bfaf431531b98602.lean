import Mathlib

theorem number_theory_232424 (p l : ℕ) (h₀ : p < 1000) (h₁ : l < 100)
    (h₂ : p + l = 144) (h₃ : 100 * (l % 10) + 10 * ((p / 10) % 10) + p % 10 +
      10 * (l / 10) + l % 10 = 603) :
    p = 115 ∧ l = 33 := by
  have h₄ : l = 144 - p := by
    omega
  rw [h₄] at h₃
  have h₅ : p ≤ 144 := by
    omega
  have h₆ : p < 1000 := h₀
  interval_cases p <;> omega