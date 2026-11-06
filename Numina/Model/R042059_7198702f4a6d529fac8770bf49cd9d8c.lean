import Mathlib

theorem algebra_194658 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : 120 / x = 120 / y + 6) (h2 : 120 / (x * (1 + 1 / 4)) = 120 / (y * (1 + 1 / 5)) + 4) :
    x = 4 ∧ y = 5 := by
  have eq3 : 120 / (x * (1 + 1 / 4)) = (120 / x) * (4 / 5) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring
  have eq4 : 120 / (y * (1 + 1 / 5)) = (120 / y) * (5 / 6) := by
    field_simp
    <;> ring_nf
    <;> field_simp
    <;> ring
  rw [eq3, eq4] at h2
  have eq5 : 120 / x = 120 / y + 6 := h1
  have eq7 : (120 / y + 6) * (4 / 5) = (120 / y) * (5 / 6) + 4 := by
    have h5 : (120 / x) = (120 / y + 6) := by
      linarith
    rw [h5] at h2
    linarith
  have eq8 : (120 / y) = 24 := by
    field_simp at eq7 ⊢
    nlinarith
    all_goals nlinarith
  have eq9 : y = 5 := by
    field_simp at eq8 ⊢
    nlinarith
  have eq10 : 120 / x = 30 := by
    have eq5 : 120 / x = 120 / y + 6 := h1
    rw [show (120 / y : ℝ) = 24 by linarith [eq8] ] at eq5
    linarith
  have eq11 : x = 4 := by
    field_simp at eq10 ⊢
    nlinarith
  exact ⟨eq11, eq9⟩