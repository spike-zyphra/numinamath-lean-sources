import Mathlib

theorem algebra_291547 (a b c d e f : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1) (he : e = 1 ∨ e = -1) (hf : f = 1 ∨ f = -1)
    (x : ℝ) (hx : x = a - b + c - d + e - f) :
    x = -6 ∨ x = -4 ∨ x = -2 ∨ x = 0 ∨ x = 2 ∨ x = 4 ∨ x = 6 := by
  rw [hx]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;> rcases hd with hd | hd <;> rcases he with he | he <;> rcases hf with hf | hf <;> simp [ha, hb, hc, hd, he, hf] <;> norm_num
  <;> try { tauto }
  <;> norm_num
  <;> try { simp }
  <;> try { norm_num }
  <;> try { tauto }
  <;> norm_num
  <;> try { simp }
  <;> try { norm_num }
  <;> try { tauto }
  <;> norm_num
  <;> try { simp }
  <;> try { norm_num }
  <;> try { tauto }