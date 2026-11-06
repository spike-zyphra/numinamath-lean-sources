import Mathlib

theorem algebra_287857 (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (h1 : a * b = 2) (h2 : b * c = 3) (h3 : c * d = 4)
    (h4 : d * e = 15) (h5 : e * a = 10) : a = 4 / 3 := by
  have hb_eq : b = 2 / a := by
    field_simp
    nlinarith
  have hc_eq : c = 3 * a / 2 := by
    rw [hb_eq] at h2
    field_simp at h2 ⊢
    nlinarith
  have hd_eq : d = 8 / (3 * a) := by
    rw [hc_eq] at h3
    field_simp at h3 ⊢
    nlinarith
  have he_eq : e = 45 * a / 8 := by
    rw [hd_eq] at h4
    field_simp at h4 ⊢
    nlinarith
  rw [he_eq] at h5
  have ha_eq : a = 4 / 3 := by
    nlinarith
  exact ha_eq