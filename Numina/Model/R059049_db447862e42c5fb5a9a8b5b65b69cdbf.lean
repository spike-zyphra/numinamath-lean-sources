import Mathlib

theorem algebra_94803 (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (h : b / (a * c) = x / (d * e)) :
    x = b * d * e / (a * c) := by
  have h1 : b * (d * e) = a * c * x := by
    field_simp [(show a * c ≠ 0 by positivity), (show d * e ≠ 0 by positivity)] at h ⊢
    nlinarith
  have h2 : x = (b * (d * e)) / (a * c) := by
    field_simp [(show a * c ≠ 0 by positivity)]
    nlinarith
  rw [h2]
  <;> ring_nf <;> tauto