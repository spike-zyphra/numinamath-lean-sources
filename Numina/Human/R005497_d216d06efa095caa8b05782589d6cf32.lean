import Mathlib

open Complex

/-Given that $\sin A+\sin B=1$ and $\cos A+\cos B=3 / 2$, what is the value of $\cos (A-B)$ ?-/
theorem algebra_608512 (A B : ℂ) : sin A + sin B = 1 → cos A + cos B = 3 / 2 → cos (A - B) = 5 / 8 := by
-- Rewrite the two assumptions by trig identities sin_add_sin and cos_add_cos
  intro hsin hcos; rw [sin_add_sin] at hsin; rw [cos_add_cos] at hcos
-- Divide the two assumptions and solve for $tan (A+B)/2$
  let h'sin := hsin; apply_fun fun t => t / (2 * cos ((A + B) / 2) * cos ((A - B) / 2)) at h'sin
  nth_rw 2 [hcos] at h'sin; rw [mul_div_mul_right, mul_div_mul_left, ← tan_eq_sin_div_cos] at h'sin
  rw [one_div_div] at h'sin
-- Compute the square of $sin (A+B)/2$
  have : cos ((A + B) / 2) ≠ 0 := by intro h; simp [h] at hcos; norm_num at hcos
  have aux1 := tan_sq_div_one_add_tan_sq this; simp [h'sin] at aux1; norm_num at aux1
-- Take squares on both sides of hsin, then plug in the value of the square of $sin (A+B)/2$
  apply_fun fun t => t ^ 2 at hsin; rw [mul_pow, mul_pow, ← aux1] at hsin; norm_num at hsin
  rw [mul_comm, mul_eq_one_iff_eq_inv₀] at hsin; rw [show A-B = 2*((A-B)/2) by ring]
-- Rewrite the goal by cos_two_mul and plug in the value of the square of $cos (A-B)/2$
  rw [cos_two_mul, hsin]; any_goals norm_num
  intro h; simp [h] at hcos; norm_num at hcos