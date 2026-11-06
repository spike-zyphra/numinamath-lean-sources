import Mathlib

theorem algebra_93867 {m s : ℕ} (h₀ : m ≠ 0) (h₁ : s ≠ 0)
    (h₂ : (30 / 100 : ℝ) * m = (80 / 100 : ℝ) * s) (h₃ : s = 15) :
    m = 40 := by
  have h₄ : (s : ℝ) = (15 : ℝ) := by 
    exact_mod_cast h₃
  rw [h₄] at h₂
  have h₅ : (m : ℝ) = (40 : ℝ) := by
    linarith
  exact_mod_cast h₅