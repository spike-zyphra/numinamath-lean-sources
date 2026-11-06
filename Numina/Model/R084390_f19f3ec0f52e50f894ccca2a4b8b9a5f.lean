import Mathlib

theorem algebra_151529 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a / b = 1 / 2) (h2 : b / c = 2 / 3) (h3 : 2 * a + 3 * b + 4 * c = 10)
    (h4 : 14 * a + 10 * b + 2 * c = x) :
    x = 20 := by
  have ne1 : b ≠ 0 := by linarith
  have ne2 : c ≠ 0 := by linarith
  have h1' : 2 * a = b := by
    field_simp at h1
    linarith
  have h2' : 3 * b = 2 * c := by
    field_simp at h2
    linarith
  have h2'' : c = 3 * a := by
    have eq1 : b = 2 * a := by linarith [h1']
    rw [eq1] at h2'
    linarith
  have h3' : 2 * a + 3 * (2 * a) + 4 * (3 * a) = 10 := by
    have eq1 : b = 2 * a := by linarith [h1']
    have eq2 : c = 3 * a := by
      linarith [h2'']
    rw [eq1, eq2] at h3
    linarith
  have ha' : a = 1 / 2 := by
    linarith
  have hb' : b = 1 := by
    linarith [h1', ha']
  have hc' : c = 3 / 2 := by
    linarith [h2'', ha']
  have hx : x = 20 := by
    rw [show a = 1 / 2 by linarith [ha']] at h4
    rw [show b = 1 by linarith [hb']] at h4
    rw [show c = 3 / 2 by linarith [hc']] at h4
    linarith
  linarith [hx]