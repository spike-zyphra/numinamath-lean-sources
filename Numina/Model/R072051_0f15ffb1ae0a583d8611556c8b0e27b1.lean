import Mathlib

theorem algebra_171100 (a b c n : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : (a + b) / a = 3) (h2 : (b + c) / b = 4) (h3 : (c + a) / c = n) :
    n = 7 / 6 := by
  have eq1 : a + b = 3 * a := by
    have h1' : a ≠ 0 := by linarith
    field_simp [h1'] at h1
    linarith
  have h4 : b = 2 * a := by
    linarith
  have eq2 : b + c = 4 * b := by
    have h2' : b ≠ 0 := by linarith
    field_simp [h2'] at h2
    linarith
  have h5 : c = 3 * b := by
    linarith
  have h6 : c = 6 * a := by
    rw [h4] at h5
    nlinarith
  have eq3 : c + a = n * c := by
    have h3' : c ≠ 0 := by linarith
    field_simp [h3'] at h3
    linarith
  rw [h6] at eq3
  have ha' : a ≠ 0 := by linarith
  have eq4 : 7 * a = 6 * n * a := by
    nlinarith
  have eq5 : 7 = 6 * n := by
    apply (mul_left_inj' ha').mp
    linarith
  linarith