import Mathlib

theorem algebra_19740 {a b c d : ℝ} (hab : a / b = 3 / 5) (hbc : b / c = 15 / 6)
    (hcd : c / d = 6) : a / d = 9 := by
  have h1 : b ≠ 0 := by
    by_contra h
    rw [h] at hab
    norm_num at hab
    all_goals linarith

  have h2 : c ≠ 0 := by
    by_contra h
    rw [h] at hbc
    norm_num at hbc
    all_goals linarith

  have h3 : d ≠ 0 := by
    by_contra h
    rw [h] at hcd
    norm_num at hcd
    all_goals linarith

  have eq1 : 5 * a = 3 * b := by
    have h4 : b ≠ 0 := h1
    field_simp at hab
    linarith

  have eq2 : 2 * b = 5 * c := by
    have h5 : c ≠ 0 := h2
    field_simp at hbc
    linarith

  have eq3 : c = 6 * d := by
    have h6 : d ≠ 0 := h3
    field_simp at hcd
    linarith

  have eq4 : b = 15 * d := by
    linarith [eq2, eq3]

  have eq5 : a = 9 * d := by
    have eq6 : 5 * a = 3 * b := eq1
    rw [eq4] at eq6
    linarith

  have eq7 : a / d = 9 := by
    have h3' : d ≠ 0 := h3
    have eq8 : a = 9 * d := eq5
    field_simp [h3']
    linarith [eq8]

  exact eq7