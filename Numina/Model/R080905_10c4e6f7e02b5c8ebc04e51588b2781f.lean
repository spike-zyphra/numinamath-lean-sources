import Mathlib

theorem number_theory_291426 {a b : ℕ} (ha : a = 2^155) (hb : b = 3^65) :
    a^13 * b^31 = 6^2015 := by
  rw [ha, hb]
  norm_num