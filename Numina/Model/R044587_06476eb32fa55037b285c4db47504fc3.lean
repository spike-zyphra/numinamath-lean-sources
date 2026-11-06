import Mathlib

theorem number_theory_269019 (b g : ℕ) (h₀ : b + g < 500) (h₁ : b * g ≠ 0)
    (h₂ : (b / (b + g : ℝ)) * 100 = g) :
    (b = 320 ∧ g = 80) ∨ (b = 225 ∧ g = 75) ∨ (b = 90 ∧ g = 60) ∨
    (b = 50 ∧ g = 50) ∨ (b = 5 ∧ g = 20) := by
  have h3 : (b : ℝ) * 100 = (g : ℝ) * (b + g) := by
    have hne : (b + g : ℝ) ≠ 0 := by
      by_contra h
      have : (b + g : ℝ) = 0 := by linarith
      have h3 : (b * g : ℝ) = 0 := by
        have hb : (b : ℝ) = 0 := by
          nlinarith [show (b + g : ℝ) = 0 by linarith, show (g : ℝ) ≥ 0 by positivity]
        rw [hb]
        norm_num
      have h4 : b * g = 0 := by
        exact_mod_cast h3
      have h5 : b * g ≠ 0 := h₁
      contradiction
    field_simp [hne] at h₂
    nlinarith
  have h4 : b * 100 = g * (b + g) := by
    exact_mod_cast h3
  have h5 : b ≤ 499 := by
    omega
  have h6 : g ≤ 499 := by
    omega
  interval_cases g <;> omega