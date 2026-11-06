import Mathlib

open Real Set
open scoped Real

theorem algebra_628232 (x : ℝ) (hx : x ∈ Ioo 0 (π / 2)) (h : cos x = 12 / 15) :
    (cos x - sin x) / (cos x + sin x) = 1 / 7 := by
  rw [mem_Ioo] at hx
  have h1 : cos x = 4 / 5 := by
    rw [h]
    norm_num
  have h2 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    exact hx.left
    linarith [hx.right, Real.pi_pos]
  have h3 : sin x = 3 / 5 := by
    have : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [h1] at this
    nlinarith [h2]
  rw [h1, h3]
  norm_num