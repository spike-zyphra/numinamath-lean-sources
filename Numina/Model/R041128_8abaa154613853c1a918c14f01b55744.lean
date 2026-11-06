import Mathlib

theorem algebra_173525 {p p1 p2 : ℝ} (hp : 0 < p1) (hp1 : p1 < p) (hp2 : p < p2)
    (h : p2 < 100) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x > 0 ∧ y > 0)
    (h1 : (x * p1 + y * p2) / (x + y) = p) :
    x / y = (p2 - p) / (p - p1) := by
  have h2 : x + y > 0 := by
    linarith
  have eq1 : x * p1 + y * p2 = p * (x + y) := by
    have hne : x + y ≠ 0 := by linarith
    field_simp [hne] at h1 ⊢
    linarith
  have eq3 : x * (p1 - p) = y * (p - p2) := by
    linarith [eq1]
  have eq4 : x / y = (p2 - p) / (p - p1) := by
    have hne1 : y ≠ 0 := by linarith
    have hne2 : p - p1 ≠ 0 := by
      linarith
    have eq5 : x / y = (p - p2) / (p1 - p) := by
      have hne1 : y ≠ 0 := by linarith
      have hne2 : p1 - p ≠ 0 := by
        linarith
      have eq6 : x * (p1 - p) = y * (p - p2) := by
        linarith [eq3]
      field_simp [hne1, hne2] at eq6 ⊢
      <;> nlinarith [eq6, sq_pos_of_pos hx, sq_pos_of_pos hy]
    have eq7 : x / y = (p2 - p) / (p - p1) := by
      rw [eq5]
      have hne : p1 - p ≠ 0 := by linarith
      have hne' : p - p1 ≠ 0 := by linarith
      field_simp [hne, hne'] at *
      <;> ring_nf
      <;> nlinarith
    linarith [eq7]
  exact eq4