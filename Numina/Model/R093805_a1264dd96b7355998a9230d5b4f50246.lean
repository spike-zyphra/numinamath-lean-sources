import Mathlib

theorem algebra_158172 (p : Fin 3 → ℝ) (h₀ : p 0 + p 1 + p 2 = 1)
    (h₁ : p 0 * (-1) + p 1 * 0 + p 2 * 1 = 0.1) (h₂ : p 0 * (-1)^2 + p 1 * 0^2 + p 2 * 1^2 = 0.9) :
    p 0 = 0.4 ∧ p 1 = 0.1 ∧ p 2 = 0.5 := by
  have eq2' : -p 0 + p 2 = (0.1 : ℝ) := by
    ring_nf at h₁ ⊢
    linarith
  have eq3' : p 0 + p 2 = (0.9 : ℝ) := by
    ring_nf at h₂ ⊢
    linarith
  have hp2 : p 2 = (0.5 : ℝ) := by
    ring_nf at eq2' eq3' ⊢
    linarith
  have hp0 : p 0 = (0.4 : ℝ) := by
    rw [hp2] at eq3'
    ring_nf at eq3' ⊢
    linarith
  have hp1 : p 1 = (0.1 : ℝ) := by
    rw [hp0, hp2] at h₀
    ring_nf at h₀ ⊢
    linarith
  exact ⟨hp0, hp1, hp2⟩