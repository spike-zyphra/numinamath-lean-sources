import Mathlib

theorem algebra_677 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) 
    (h1 : 1 / (b - a) = 30) 
    (h2 : 1 / (2 * b - a) = 10) :
    1 / (3 * b) = 5 := by
  have eq1 : b - a ≠ 0 := by
    by_contra h
    rw [h] at h1
    field_simp at h1
  have eq2 : 2 * b - a ≠ 0 := by
    by_contra h
    rw [h] at h2
    field_simp at h2
  have eq3 : b - a = 1 / 30 := by
    have h_nz : b - a ≠ 0 := eq1
    field_simp at h1 ⊢
    linarith
  have eq4 : 2 * b - a = 1 / 10 := by
    have h_nz : 2 * b - a ≠ 0 := eq2
    field_simp at h2 ⊢
    linarith
  have eq5 : b = 1 / 15 := by
    linarith [eq3, eq4]
  have eq7 : 3 * b = 1 / 5 := by
    linarith [eq5]
  have h3b_nz : 3 * b ≠ 0 := by
    linarith [hb]
  rw [eq7]
  field_simp