import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_629486 {y : ℕ} (hy : ∃ x : ℝ, y = 2021 / (x^2 - 8 * x + 60)) :
    y ≤ 45 := by
  rcases hy with ⟨x, hx⟩
  have hx2 : (x^2 - 8 * x + 60 : ℝ) > 0 := by
    nlinarith [sq_nonneg (x - 4)]
  
  have eq1 : 2021 = (y : ℝ) * (x^2 - 8 * x + 60) := by
    have hne : (x^2 - 8 * x + 60 : ℝ) ≠ 0 := by
      linarith
    field_simp [hne] at hx
    nlinarith
  
  have h2 : (x^2 - 8 * x + 60 : ℝ) ≥ 44 := by
    nlinarith [sq_nonneg (x - 4)]
  
  have h3 : (y : ℝ) > 0 := by
    nlinarith
  
  have h4 : (y : ℝ) ≤ (2021 / 44 : ℝ) := by
    nlinarith
  
  have hy2 : y ≤ 45 := by
    by_contra h
    push_neg at h
    have h5 : y ≥ 46 := by omega
    have h6 : (y : ℝ) ≥ (46 : ℝ) := by exact_mod_cast h5
    nlinarith
  
  exact hy2