import Mathlib

theorem algebra_12706 (a : ℕ → ℝ) (h₀ : a 0 = 2048) (h₁ : a 1 = 512)
    (h₂ : a 2 = 128) (h₃ : ∃ c, ∀ n, a (n + 1) = c * a n) :
    a 3 + a 4 = 40 := by
  rcases h₃ with ⟨c, hc⟩
  have hc0 := hc 0
  rw [h₀] at hc0
  rw [h₁] at hc0
  have hc1 := hc 1
  rw [h₁] at hc1
  rw [h₂] at hc1
  have c_eq : c = 1 / 4 := by
    nlinarith
  have ha3 : a 3 = c * a 2 := by
    specialize hc 2
    simpa using hc
  have ha4 : a 4 = c * a 3 := by
    specialize hc 3
    simpa using hc
  rw [c_eq, h₂] at ha3
  have a3_eq : a 3 = 32 := by
    nlinarith
  rw [c_eq, a3_eq] at ha4
  have a4_eq : a 4 = 8 := by
    nlinarith
  linarith [a3_eq, a4_eq]