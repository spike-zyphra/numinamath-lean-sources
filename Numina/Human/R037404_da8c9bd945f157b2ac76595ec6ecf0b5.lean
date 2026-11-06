import Mathlib

open Real

/- $3.452 A=\operatorname{tg}\left(\frac{3 \pi}{4}-\frac{1}{4} \arcsin \left(-\frac{4}{5}\right)\right)$

$3.452 A=\tan\left(\frac{3 \pi}{4}-\frac{1}{4} \arcsin \left(-\frac{4}{5}\right)\right)$ -/
theorem algebra_196422 : tan (3 * π / 4 - (arcsin (-4 / 5)) / 4) = (1 - √5) / 2 := by
  -- Prove that tan (x / 2) = sin x / (1 + cos x) for all x
  have tan_div_two x : tan (x / 2) = sin x / (1 + cos x) := by
    -- We have sin x = sin (2 * (x / 2)) = 2 * sin (x / 2) * cos (x / 2)
    -- and 1 + cos x = 1 + cos (2 * (x / 2)) = 2 * cos (x / 2) * cos (x / 2).
    nth_rw 2 3 [show x = 2 * (x / 2) by ring]
    rw [sin_two_mul, cos_two_mul, show 1 + (2 * cos (x / 2)^2 - 1) = 2 * cos (x / 2) * cos (x / 2) by ring]
    simp_rw [mul_assoc, mul_div_mul_left _ _ (show (2 : ℝ) ≠ 0 by norm_num)]
    rw [tan_eq_sin_div_cos]
    -- If cos (x / 2) = 0 then the result follows from Lean's definition of division by zero.
    by_cases h : cos (x / 2) = 0
    · simp [h]
    -- If cos (x / 2) ≠ 0 then the right hand side simplifies to sin (x / 2) / cos (x / 2) = tan (x / 2).
    · rw [mul_div_mul_right _ _ h]
  -- We have arcsin(-4/5) = -arcsin(4/5).
  rw [neg_div, arcsin_neg, neg_div, sub_neg_eq_add]
  -- Let a = arcsin(4 / 5).
  set a := arcsin (4 / 5)
  -- 0 ≤ a because 0 ≤ 4 / 5.
  have ha0 : 0 ≤ a := by rw [arcsin_nonneg]; norm_num
  -- a ≤ π / 2 from the definition of arcsin.
  have ha1 : a ≤ π / 2 := arcsin_le_pi_div_two _
  -- Rewrite the goal as follows:
  -- tan (3π / 4 + a / 4) = tan ((a / 2 - π / 2) / 2 + π) = tan ((a / 2 - π / 2) / 2).
  -- Use the identity for tan (x / 2) and get the following goal:
  -- sin (a / 2 - π / 2) / (1 + cos (a / 2 - π / 2)) = (1 - √5) / 2.
  rw [show 3 * π / 4 + a / 4 = (a / 2 - π / 2) / 2 + π by ring, tan_add_pi, tan_div_two]
  -- sin (a / 2 - π / 2) = -cos(a / 2) and cos(a / 2 - π / 2) = sin(a / 2).
  rw [sin_sub_pi_div_two, cos_sub_pi_div_two]
  -- Show that sin (a / 2) = 1 / √5.
  have hsin : sin (a / 2) = 1 / √5 := by
    -- We have the following identity: sin (a / 2) = √((1 - cos a) / 2) for a ∈ [0, 2π].
    rw [sin_half_eq_sqrt ha0 (by linarith)]
    -- cos(a) = cos(arcsin(4 / 5)) = √(1 - (4 / 5)^2).
    rw [cos_arcsin]
    norm_num
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num]
    rw [sqrt_sq (by norm_num), sqrt_sq (by norm_num)]
    field_simp
    norm_num [mul_comm]
  -- Show that cos (a / 2) = 2 / √5.
  have hcos : cos (a / 2) = 2 / √5 := by
    -- We have that cos (a / 2) = √(1 - sin (a / 2)) for a ∈ [-π / 2, π / 2].
    rw [cos_eq_sqrt_one_sub_sin_sq (by linarith) (by linarith), hsin]
    -- cos (a / 2) = √(1 - 1 / 5) = √4 / √5 = 2 / √5.
    norm_num
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  -- Use the values of sin(a / 2) and cos(a / 2), simplify the goal and get the result.
  rw [hsin, hcos]
  field_simp
  ring_nf
  simp_rw [show 3 = 2 + 1 by norm_num, pow_add, sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  ring