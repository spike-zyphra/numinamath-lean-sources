import Mathlib

theorem algebra_612687 {a b : ℝ} (h : a^2 - 11*a*b - 60 = 0) (ha : a ≠ 0) :
    b = (a^2 - 60)/(11*a) := by
  have h1 : a^2 - 60 = 11 * a * b := by 
    linarith
  have h2 : b = (a^2 - 60) / (11 * a) := by
    have hne : 11 * a ≠ 0 := by
      intro h'
      have : a = 0 := by
        linarith
      contradiction
    have eq1 : 11 * a * b = a^2 - 60 := by
      linarith
    have eq2 : b = (a^2 - 60) / (11 * a) := by
      field_simp [hne]
      <;> nlinarith
    exact eq2
  rw [h2]
  <;> field_simp [ha]
  <;> ring_nf
  <;> field_simp [ha]
  <;> nlinarith