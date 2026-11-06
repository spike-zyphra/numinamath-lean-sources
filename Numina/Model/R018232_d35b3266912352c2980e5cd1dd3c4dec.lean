import Mathlib

theorem algebra_73663 {a b c : ℤ} (ha : a ≥ 4) (hb : b ≥ 4) (hc : c ≥ 4)
    (hne : ¬(a = b ∧ b = c)) (h : 4 * a * b * c = (a + 3) * (b + 3) * (c + 3)) :
    a + b + c = 16 := by
  have h1 : a ≤ 12 := by
    nlinarith [sq_nonneg (a - 12 : ℤ), sq_nonneg (b - 12 : ℤ), sq_nonneg (c - 12 : ℤ), 
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb), 
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc), 
      mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  have h2 : b ≤ 12 := by
    nlinarith [sq_nonneg (a - 12 : ℤ), sq_nonneg (b - 12 : ℤ), sq_nonneg (c - 12 : ℤ), 
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb), 
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc), 
      mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  have h3 : c ≤ 12 := by
    nlinarith [sq_nonneg (a - 12 : ℤ), sq_nonneg (b - 12 : ℤ), sq_nonneg (c - 12 : ℤ), 
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb), 
      mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hc), 
      mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)]
  interval_cases a <;> interval_cases b <;> omega