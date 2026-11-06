import Mathlib

theorem algebra_176769 (b c : ℝ) (hb : b > 0) (hc : c > 0)
    (h1 : b / (v + c) = b / v - 2 / 60) (h2 : b / (v - c) = b / v + 2 / 60) :
    v = (Real.sqrt (c^2 + 120)) / 2 := by
  have h3 : v ≠ 0 := by
    by_contra h
    rw [h] at h1
    field_simp at h1
    all_goals nlinarith
  have h4 : v + c ≠ 0 := by
    by_contra h
    rw [h] at h1
    field_simp at h1
    all_goals nlinarith
  have h5 : v - c ≠ 0 := by
    by_contra h
    rw [h] at h2
    field_simp at h2
    all_goals nlinarith
  field_simp [show v + c ≠ 0 by assumption, show v ≠ 0 by assumption] at h1
  field_simp [show v - c ≠ 0 by assumption, show v ≠ 0 by assumption] at h2
  have eq1 : v^2 + c * v - 30 * b * c = 0 := by
    nlinarith
  have eq2 : v^2 - c * v - 30 * b * c = 0 := by
    nlinarith
  have h6 : 2 * c * v = 0 := by
    nlinarith [eq1, eq2]
  have h8 : v = 0 := by
    nlinarith [show c ≠ 0 by linarith [hc]]
  contradiction