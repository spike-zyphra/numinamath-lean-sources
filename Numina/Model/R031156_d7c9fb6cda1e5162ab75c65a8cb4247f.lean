import Mathlib

theorem algebra_21304 (veal price x : ℝ) (hv : veal = 3) (hp : price = 2.20) (h : x * price = veal) :
    (round (100 * x) : ℝ) / 100 = 1.36 := by
  rw [hv, hp] at h
  have hx : x = 3 / 2.20 := by 
    field_simp at h ⊢ 
    linarith
  rw [hx]
  norm_num [round_eq]