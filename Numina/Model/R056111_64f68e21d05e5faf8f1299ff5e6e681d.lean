import Mathlib

theorem algebra_301056 {a b c d e f : ℝ} (ha : a / b = 2 / 3) (hb : c / d = 2 / 3) (hc : e / f = 2 / 3) :
    (a^(-2 : ℤ) + 2^(-2 : ℤ) * c^(-2 : ℤ) + 3^(-3 : ℤ) * e^(-2 : ℤ) +
     4^(-4 : ℤ) * 2^(-2 : ℤ)) / (b^(-2 : ℤ) + 2^(-2 : ℤ) * d^(-2 : ℤ) +
     3^(-3 : ℤ) * f^(-2 : ℤ) + 4^(-4 : ℤ) * 3^(-2 : ℤ)) = 9 / 4 := by
  have h1 : b ≠ 0 := by
    by_contra h
    have h2 : b = 0 := by linarith
    rw [h2] at ha
    norm_num at ha
  have h2 : d ≠ 0 := by
    by_contra h
    have h3 : d = 0 := by linarith
    rw [h3] at hb
    norm_num at hb
  have h3 : f ≠ 0 := by
    by_contra h
    have h4 : f = 0 := by linarith
    rw [h4] at hc
    norm_num at hc
  have h4 : a = 2 / 3 * b := by
    field_simp [h1] at ha
    linarith
  have h5 : c = 2 / 3 * d := by
    field_simp [h2] at hb
    linarith
  have h6 : e = 2 / 3 * f := by
    field_simp [h3] at hc
    linarith
  simp [zpow_neg, zpow_ofNat, h4, h5, h6] at *
  <;> field_simp [h1, h2, h3] at *
  <;> ring_nf
  <;> field_simp [h1, h2, h3] at *
  <;> nlinarith
  all_goals norm_num
  <;> nlinarith