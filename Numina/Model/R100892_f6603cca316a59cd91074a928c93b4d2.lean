import Mathlib

theorem algebra_6273 {A B C D : ℝ} (hA : A / B = 1 / 2) (hB : B / C = 3 / 4)
    (hC : C / D = 5 / 6) (hABCD : A + B + C + D = 1064) : A = 120 := by
  have h1 : B ≠ 0 := by
    by_contra h
    rw [h] at hA
    norm_num at hA
  have h2 : C ≠ 0 := by
    by_contra h
    rw [h] at hB
    norm_num at hB
  have h3 : D ≠ 0 := by
    by_contra h
    rw [h] at hC
    norm_num at hC

  have eq1 : 2 * A = B := by
    have h4 : B ≠ 0 := h1
    field_simp [h4] at hA
    linarith

  have eq2 : 4 * B = 3 * C := by
    have h5 : C ≠ 0 := h2
    field_simp [h5] at hB
    linarith

  have eq3 : 6 * C = 5 * D := by
    have h6 : D ≠ 0 := h3
    field_simp [h6] at hC
    linarith

  have eq4 : B = 2 * A := by
    linarith [eq1]

  have eq5 : C = 8 / 3 * A := by
    rw [eq4] at eq2
    linarith

  have eq6 : D = 16 / 5 * A := by
    rw [eq5] at eq3
    linarith

  rw [eq4, eq5, eq6] at hABCD
  linarith