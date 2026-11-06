import Mathlib

theorem number_theory_282207 (total_mins : ℕ) (h₀ : total_mins ≠ 0)
    (green_mins red_mins : ℕ) (h₁ : green_mins + red_mins = total_mins)
    (h₂ : (green_mins / total_mins : ℝ) = 75 / 100) :
    green_mins * 1 = red_mins * 3 := by

  have h3 : (total_mins : ℝ) ≠ 0 := by
    exact_mod_cast show (total_mins : ℕ) ≠ 0 by exact h₀

  have eq1 : (green_mins : ℝ) / (total_mins : ℝ) = (75 / 100 : ℝ) := by
    simpa using h₂

  have eq2 : (green_mins : ℝ) = (75 / 100 : ℝ) * (total_mins : ℝ) := by
    have htne : (total_mins : ℝ) ≠ 0 := h3
    field_simp [htne] at eq1 ⊢
    linarith

  have eq3 : (green_mins : ℝ) + (red_mins : ℝ) = (total_mins : ℝ) := by
    exact_mod_cast (show green_mins + red_mins = total_mins by linarith)

  have eq4 : (100 : ℝ) * (green_mins : ℝ) = 75 * (total_mins : ℝ) := by
    have htne : (total_mins : ℝ) ≠ 0 := h3
    have : (green_mins : ℝ) = (75 / 100 : ℝ) * (total_mins : ℝ) := eq2
    linarith

  have eq5 : 100 * (green_mins : ℕ) = 75 * (total_mins : ℕ) := by
    exact_mod_cast eq4

  have eq8 : total_mins = green_mins + red_mins := by
    linarith

  rw [eq8] at eq5

  have eq9 : 25 * (green_mins : ℕ) = 75 * (red_mins : ℕ) := by
    linarith

  have eq10 : (green_mins : ℕ) = 3 * (red_mins : ℕ) := by
    omega

  linarith