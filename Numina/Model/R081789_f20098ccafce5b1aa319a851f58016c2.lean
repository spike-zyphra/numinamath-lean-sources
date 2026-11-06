import Mathlib

theorem algebra_133568 {a b c d e f : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (h : a * 2^5 + b * 2^4 + c * 2^3 + d * 2^2 + e * 2 + f = 11) :
    a * 3^5 + b * 3^4 + c * 3^3 + d * 3^2 + e * 3 + f = 142 := by
  rcases ha with (ha | ha)
  <;> rcases hb with (hb | hb)
  <;> rcases hc with (hc | hc)
  <;> rcases hd with (hd | hd)
  <;> rcases he with (he | he)
  <;> rcases hf with (hf | hf)
  <;> norm_num [ha, hb, hc, hd, he, hf] at h ⊢
  <;> omega