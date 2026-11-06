import Mathlib

theorem algebra_661 (d c t : ℝ) (hc : c ≠ 0) (ht : t ≠ 0) (h3 : 3 * d = 5 * c) (h5 : 5 * d = 7 * t)
    (h6 : 3 * t = 5 * c) (h7 : 5 * t = 7 * d) (h8 : c * t = 300 / 11) :
    d * t = 8437.5 ∧ c * t = 23437.5 ∧ t * 300 = 16537.5 := by 
  have h9 : 3 * d = 3 * t := by
    nlinarith [h3, h6]
  have eq2 : d = t := by
    apply (mul_left_inj' (show (3 : ℝ) ≠ 0 by norm_num)).mp
    linarith [h9]
  have eq3 : 5 * d = 7 * t := by linarith [h5]
  rw [show d = t by linarith [eq2]] at eq3
  have eq4 : t = 0 := by
    nlinarith 
  contradiction