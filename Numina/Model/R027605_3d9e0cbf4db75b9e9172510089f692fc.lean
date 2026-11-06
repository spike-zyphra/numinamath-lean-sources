import Mathlib

theorem algebra_272000 (A B C D : ℝ) (h₀ : A < B) (h₁ : B < C) (h₂ : C < D)
    (h₃ : (B - A) / (C - A) = 1 / 5) (h₄ : (C - B) / (D - C) = 2 / 1) :
    (B - A) / (D - C) = 1 / 2 := by
  have h5 : C - A ≠ 0 := by linarith
  have h6 : D - C ≠ 0 := by linarith
  have eq1 : 5 * (B - A) = C - A := by
    field_simp [h5] at h₃
    linarith
  have eq2 : (C - B) = 2 * (D - C) := by
    field_simp [h6] at h₄
    linarith
  have eq4 : C - B = 4 * (B - A) := by
    have eq5 : C - A = 5 * (B - A) := by
      linarith
    have eq6 : C - A = (B - A) + (C - B) := by
      linarith
    linarith [eq5, eq6]
  have eq8 : 2 * (B - A) = (D - C) := by
    linarith [eq2, eq4]
  have eq9 : D - C ≠ 0 := by linarith
  have eq10 : B - A ≠ 0 := by linarith
  field_simp [eq9]
  linarith [eq8]