import Mathlib

open Real

theorem algebra_3215 : (sqrt 28 + sqrt 20) * (sqrt 45 - sqrt 63) = -12 := by
  have h1 : sqrt 28 = 2 * sqrt 7 := by
    rw [sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)] 
    ring_nf; norm_num
  have h2 : sqrt 20 = 2 * sqrt 5 := by
    rw [sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)] 
    ring_nf; norm_num
  have h3 : sqrt 45 = 3 * sqrt 5 := by
    rw [sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)] 
    ring_nf; norm_num
  have h4 : sqrt 63 = 3 * sqrt 7 := by
    rw [sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)] 
    ring_nf; norm_num
  rw [h1, h2, h3, h4]
  ring_nf
  norm_num