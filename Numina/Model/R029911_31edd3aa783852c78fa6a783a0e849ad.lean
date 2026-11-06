import Mathlib

theorem algebra_180562 {m : ℝ} (h : m ≠ 0) (f : ℝ → ℝ → ℝ)
    (hf : ∀ x y, f x y = 4 * x * y / (m * x + 3 * y)) (h1 : f 1 2 = 1) :
    m = 2 ∧ f 3 12 = 24 / 7 := by

  have eq1 : f 1 2 = 4 * (1 : ℝ) * (2 : ℝ) / (m * (1 : ℝ) + 3 * (2 : ℝ)) := hf 1 2
  rw [eq1] at h1
  have h2 : m = 2 := by
    have eq2 : 4 * (1 : ℝ) * (2 : ℝ) / (m * (1 : ℝ) + 3 * (2 : ℝ)) = 8 / (m + 6) := by
      field_simp
      <;> ring_nf
    rw [eq2] at h1
    have h3 : m + 6 ≠ 0 := by 
      by_contra h3
      have h4 : m + 6 = 0 := h3
      rw [show m + 6 = (0 : ℝ) by linarith [h4]] at h1 
      norm_num at h1 
    have eq3 : 8 / (m + 6) = 1 := h1 
    have h4 : 8 = m + 6 := by
      have h5 : (m + 6) ≠ 0 := h3 
      have eq4 : 8 / (m + 6) * (m + 6) = 1 * (m + 6) := by 
        rw [eq3]
      have eq5 : 8 / (m + 6) * (m + 6) = 8 := by
        field_simp [h5]
      rw [eq5] at eq4 
      linarith 
    linarith 
  have h3 : f 3 12 = 24 / 7 := by
    rw [hf 3 12]
    rw [h2]
    norm_num 
  constructor
  · exact h2 
  · exact h3