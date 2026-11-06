import Mathlib

open Real Set

/- 289. Find the relationship between $\arcsin \cos \arcsin x$ and $\arccos \sin \arccos x$ -/
theorem algebra_130380 {x : ℝ} :
  arcsin (cos (arcsin x)) + arccos (sin (arccos x)) = π / 2
:= by
  -- First, note that arccos x = pi/2 - arcsin x
  rw [arccos_eq_pi_div_two_sub_arcsin]

  -- Then, note that sin (arccos x) = √(1 - x ^ 2)
  -- and cos (arcsin x) = √(1 - x ^ 2)
  have sin_arccos : sin (arccos x) = √(1 - x ^ 2) := by
    by_cases hx1 : -1 ≤ x; swap
    · rw [not_le] at hx1
      rw [arccos_of_le_neg_one hx1.le, sin_pi, sqrt_eq_zero_of_nonpos]
      nlinarith
    by_cases hx2 : x ≤ 1; swap
    · rw [not_le] at hx2
      rw [arccos_of_one_le hx2.le, sin_zero, sqrt_eq_zero_of_nonpos]
      nlinarith
    rw [arccos_eq_pi_div_two_sub_arcsin, sin_pi_div_two_sub, cos_arcsin]

  have cos_arcsin : cos (arcsin x) = √(1 - x ^ 2) := by
    by_cases hx1 : -1 ≤ x; swap
    · rw [not_le] at hx1
      rw [arcsin_of_le_neg_one hx1.le, cos_neg, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
      nlinarith
    by_cases hx2 : x ≤ 1; swap
    · rw [not_le] at hx2
      rw [arcsin_of_one_le hx2.le, cos_pi_div_two, sqrt_eq_zero_of_nonpos]
      nlinarith
    have : sin (arcsin x) ^ 2 + cos (arcsin x) ^ 2 = 1 := sin_sq_add_cos_sq (arcsin x)
    rw [← eq_sub_iff_add_eq', ← sqrt_inj (sq_nonneg _) (sub_nonneg.2 (sin_sq_le_one (arcsin x))), sq,
      sqrt_mul_self (cos_arcsin_nonneg _)] at this
    rw [this, sin_arcsin hx1 hx2]

  rw [sin_arccos, cos_arcsin]
  ring