import Mathlib

theorem algebra_15069 {f : ℝ → ℝ} (h : ∀ a b, b^2 * f a = a^2 * f b) (h2 : f 2 ≠ 0) :
    (f 5 - f 1) / f 2 = 6 := by
  have h1 := h 5 2
  have h2' := h 1 2
  have eq1 : f 5 = (25 / 4) * f 2 := by
    norm_num at h1 
    linarith 
  have eq2 : f 1 = (1 / 4) * f 2 := by
    norm_num at h2'
    linarith 
  have eq3 : f 5 - f 1 = 6 * f 2 := by 
    linarith [eq1, eq2]
  have eq4 : (f 5 - f 1) / f 2 = 6 := by
    have h5 : f 2 ≠ 0 := h2
    field_simp [h5]
    linarith [eq3]
  exact eq4