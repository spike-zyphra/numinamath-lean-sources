import Mathlib

theorem algebra_67651 (h m f : ℝ) (h₀ : 3 * h + 5 * m + f = 23.50) (h₁ : 5 * h + 9 * m + f = 39.50) :
    2 * h + 2 * m + 2 * f = 15 := by
  have h₂ : 2 * h + 4 * m = 16 := by
    have eq1 : (5 * h + 9 * m + f) - (3 * h + 5 * m + f) = 39.50 - 23.50 := by 
      rw [h₁, h₀]
      all_goals norm_num at *
    ring_nf at eq1 ⊢
    linarith
  have eq2 : h + m + f = 7.5 := by
    have eq3 : h = 8 - 2 * m := by
      linarith [h₂]
    rw [eq3] at h₀
    have eq4 : f = (m - 0.5 : ℝ) := by
      ring_nf at h₀ ⊢
      linarith
    rw [eq3, eq4]
    ring_nf
    <;> linarith
  linarith [eq2]
  all_goals norm_num at *
  <;> linarith