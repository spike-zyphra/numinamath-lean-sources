import Mathlib

theorem algebra_308866 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a * b = 2 * (a + b)) (h2 : b * c = 3 * (b + c)) (h3 : c * a = 4 * (a + c)) :
    a + b + c = 1128 / 35 := by
  have eq1 : 1 / a + 1 / b = 1 / 2 := by
    have hne : a * b ≠ 0 := mul_ne_zero ha hb
    field_simp at h1 ⊢
    linarith
  have eq2 : 1 / b + 1 / c = 1 / 3 := by
    have hne : b * c ≠ 0 := mul_ne_zero hb hc
    field_simp at h2 ⊢
    linarith
  have eq3 : 1 / c + 1 / a = 1 / 4 := by
    have hne : c * a ≠ 0 := mul_ne_zero hc ha
    field_simp at h3 ⊢
    linarith
  have eq4 : 1 / a + 1 / b + 1 / c = 13 / 24 := by
    linarith [eq1, eq2, eq3]
  have h4 : 1 / a = 5 / 24 := by
    have eq5 : 1 / a = (1 / a + 1 / b + 1 / c) - (1 / b + 1 / c) := by ring
    rw [eq4] at eq5
    have eq6 : (1 / b + 1 / c) = 1 / 3 := eq2
    rw [eq6] at eq5
    linarith
  have h5 : 1 / b = 7 / 24 := by
    have eq6 : 1 / b = (1 / a + 1 / b + 1 / c) - (1 / a + 1 / c) := by ring
    rw [eq4] at eq6
    have eq7 : (1 / a + 1 / c) = 1 / 4 := by linarith [eq3]
    rw [eq7] at eq6
    linarith
  have h6 : 1 / c = 1 / 24 := by
    have eq7 : 1 / c = (1 / a + 1 / b + 1 / c) - (1 / a + 1 / b) := by ring
    rw [eq4] at eq7
    have eq8 : (1 / a + 1 / b) = 1 / 2 := eq1
    rw [eq8] at eq7
    linarith
  have ha' : a = 24 / 5 := by
    have hne : a ≠ 0 := ha
    field_simp at h4 ⊢
    linarith
  have hb' : b = 24 / 7 := by
    have hne : b ≠ 0 := hb
    field_simp at h5 ⊢
    linarith
  have hc' : c = 24 := by
    have hne : c ≠ 0 := hc
    field_simp at h6 ⊢
    linarith
  rw [ha', hb', hc']
  norm_num