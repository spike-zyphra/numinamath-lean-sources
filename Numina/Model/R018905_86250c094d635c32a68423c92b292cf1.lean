import Mathlib

theorem algebra_191345 (a b c d e f : ℝ) (h₀ : a * c * e ≠ 0)
    (h₁ : ∀ x, abs (a * x + b) + abs (c * x + d) = abs (e * x + f)) :
    a * d = b * c := by
  have ha : a ≠ 0 := by
    intro ha'
    rw [ha'] at h₀
    simp at h₀
  have hc : c ≠ 0 := by
    intro hc'
    rw [hc'] at h₀
    simp at h₀
  have he : e ≠ 0 := by
    intro he'
    rw [he'] at h₀
    simp at h₀
  have h2 := h₁ (-f / e)
  have eq1 : abs (a * (-f / e) + b) + abs (c * (-f / e) + d) = abs (e * (-f / e) + f) := by
    simpa using h2
  have eq2 : abs (e * (-f / e) + f) = 0 := by
    have eq3 : e * (-f / e) + f = 0 := by
      field_simp [he]
      <;> linarith
    rw [eq3]
    norm_num
  rw [eq2] at eq1
  have h3 : abs (a * (-f / e) + b) = 0 := by
    linarith [abs_nonneg (a * (-f / e) + b), abs_nonneg (c * (-f / e) + d)]
  have h4 : abs (c * (-f / e) + d) = 0 := by
    linarith [abs_nonneg (a * (-f / e) + b), abs_nonneg (c * (-f / e) + d)]
  have eq4 : a * (-f / e) + b = 0 := by
    rwa [abs_eq_zero] at h3
  have eq5 : c * (-f / e) + d = 0 := by
    rwa [abs_eq_zero] at h4
  have eq6 : b = (a * f) / e := by
    field_simp [he] at eq4 ⊢
    linarith
  have eq7 : d = (c * f) / e := by
    field_simp [he] at eq5 ⊢
    linarith
  rw [eq6, eq7]
  field_simp [he]
  <;> ring