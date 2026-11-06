import Mathlib

theorem algebra_2412 (a b c d e f : ℚ)
    (h₀ : a / b = 1 / 2) (h₁ : b / c = 1 / 3) (h₂ : c / d = 1 / 4)
    (h₃ : d / e = 1 / 5) (h₄ : e / f = 1 / 6) : f / a = 720 := by

  have h1 : b ≠ 0 := by
    by_contra h
    rw [h] at h₀
    norm_num at h₀
  have eq1 : 2 * a = b := by
    field_simp [h1] at h₀
    linarith

  have h2 : c ≠ 0 := by
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  have eq2 : 3 * b = c := by
    field_simp [h2] at h₁
    linarith

  have h3 : d ≠ 0 := by
    by_contra h
    rw [h] at h₂
    norm_num at h₂
  have eq3 : 4 * c = d := by
    field_simp [h3] at h₂
    linarith

  have h4 : e ≠ 0 := by
    by_contra h
    rw [h] at h₃
    norm_num at h₃
  have eq4 : 5 * d = e := by
    field_simp [h4] at h₃
    linarith

  have h5 : f ≠ 0 := by
    by_contra h
    rw [h] at h₄
    norm_num at h₄
  have eq5 : 6 * e = f := by
    field_simp [h5] at h₄
    linarith

  have ha : a ≠ 0 := by
    by_contra h
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by
      linarith [eq1, ha0]
    contradiction

  have eq6 : f = 720 * a := by
    linarith [eq1, eq2, eq3, eq4, eq5]

  have h6 : f / a = 720 := by
    rw [eq6]
    field_simp [ha]
    all_goals linarith

  exact h6