import Mathlib

open Real
open scoped BigOperators

lemma two_mul_sqrt_le_add {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * √ (x * y) ≤ x + y := by
  -- Square both sides
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, add_sq, sq_sqrt (by positivity), ← sub_nonneg]
  suffices 0 ≤ (x - y) ^ 2 by linarith
  apply sq_nonneg

-- Key inequality that follows from AM-GM
lemma l_key {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) :
  8 * (x ^ (2 : ℝ) * y ^ (3 : ℝ) * z ^ (3 : ℝ)) ^ (1 / 4 : ℝ) / x ^ 2 ≤ 1 / x ^ 2 - 1 := by
  calc
    -- Remove the fourth root
    8 * (x ^ (2 : ℝ) * y ^ (3 : ℝ) * z ^ (3 : ℝ)) ^ (1 / 4 : ℝ) / x ^ 2 = (2 * √ (y * z) * 4 * √ (x * √ (y * z))) / x ^ 2 := by
      rw [div_left_inj' (by positivity)]--, ← rpow_left_inj₀ (by positivity) (by positivity) (show 4 ≠ 0 by norm_num)]
      repeat rw [mul_rpow (by positivity) (by positivity)]
      repeat rw [sqrt_eq_rpow]
      repeat rw [mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity)]
      repeat rw [← rpow_mul (by positivity)]
      norm_num
      rw [show y ^ (3 / 4 : ℝ) = y ^ (1 / 2 : ℝ) * y ^ (1 / 4 : ℝ) by rw [← rpow_add (by positivity)]; norm_num]
      rw [show z ^ (3 / 4 : ℝ) = z ^ (1 / 2 : ℝ) * z ^ (1 / 4 : ℝ) by rw [← rpow_add (by positivity)]; norm_num]
      ring
    -- Use AM-GM
    _ = (2 * √ (y * z) * 2 * (2 * √ (x * √ (y * z)))) / x ^ 2 := by ring
    -- Use AM-GM
    _ ≤ (2 * √ (y * z) * 2 * (x + √ (y * z))) / x ^ 2 := by gcongr; apply two_mul_sqrt_le_add (by positivity) (by positivity)
    _ = ((2 * √ (y * z)) * (2 * x + 2 * √ (y * z))) / x ^ 2 := by ring
    -- Use AM-GM
    _ ≤ ((y + z) * (2 * x + 2 * √ (y * z))) / x ^ 2 := by gcongr; apply two_mul_sqrt_le_add (by positivity) (by positivity)
    -- Use AM-GM
    _ ≤ ((y + z) * (2 * x + (y + z))) / x ^ 2 := by gcongr; apply two_mul_sqrt_le_add (by positivity) (by positivity)
    -- Use the condition that the numbers sum to 1
    _ = ((1 - x) * (1 + x)) / x ^ 2 := by rw [← h]; ring
    _ = (1 - x ^ 2) / x ^ 2 := by rw [mul_comm, ← sq_sub_sq, one_pow]
    _ = 1 / x ^ 2 - 1 := by rw [sub_div, div_self (by nlinarith)]

/- 18. Let the length, width, and height of a rectangular prism be $a$, $b$, and $c$, respectively, and its body diagonal be $l$. Prove:

$$

\left(l^{4}-a^{4}\right)\left(l^{4}-b^{4}\right)\left(l^{4}-c^{4}\right) \geqslant 512 a^{4} b^{4} c^{4} .

$$
 -/
theorem inequalities_161032 (a b c l : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hl : l = sqrt (a^2 + b^2 + c^2)) :
    (l^4 - a^4) * (l^4 - b^4) * (l^4 - c^4) ≥ 512 * a^4 * b^4 * c^4 := by
  have l_pos : 0 < l := by rw [hl]; positivity
  -- Divide both sides by a ^ 4 * b ^ 4 * c ^ 4
  rw [ge_iff_le, ← div_le_div_iff_of_pos_right (show 0 < a ^ 4 * b ^ 4 * c ^ 4 by positivity)]
  conv_lhs => simp [mul_assoc, mul_div_cancel_right₀ (512 : ℝ) (show a ^ 4 * (b ^ 4 * c ^ 4) ≠ 0 by positivity)]
  rw [show (l ^ 4 - a ^ 4) * (l ^ 4 - b ^ 4) * (l ^ 4 - c ^ 4) / (a ^ 4 * b ^ 4 * c ^ 4) = ((l ^ 4 - a ^ 4) / a ^ 4) * ((l ^ 4 - b ^ 4) / b ^ 4) * ((l ^ 4 -  c ^ 4) / c ^ 4) by ring]
  repeat rw [sub_div, div_self (by positivity)]
  -- Introduce new variables
  let x := a ^ 2 / l ^ 2
  let y := b ^ 2 / l ^ 2
  let z := c ^ 2 / l ^ 2
  -- Show that their sum is 1
  have sum_eq_one : x + y + z = 1 := by
    unfold x y z
    rw [hl, sq_sqrt (by positivity), div_add_div_same, div_add_div_same, div_self (by positivity)]
  -- Rewrite the inequality in terms of x, y, z
  rw [show l ^ 4 / a ^ 4 = 1 / x ^ 2 by unfold x; rw [div_pow, ← pow_mul, ← pow_mul, one_div_div]]
  rw [show l ^ 4 / b ^ 4 = 1 / y ^ 2 by unfold y; rw [div_pow, ← pow_mul, ← pow_mul, one_div_div]]
  rw [show l ^ 4 / c ^ 4 = 1 / z ^ 2 by unfold z; rw [div_pow, ← pow_mul, ← pow_mul, one_div_div]]
  -- Show that the RHS is nonnegative
  have x_expr_pos : 0 ≤ 1 / x ^ 2 - 1 := by unfold x; rw [sub_nonneg, div_pow, one_div_div, hl, sq_sqrt (by positivity), one_le_div (by positivity)]; nlinarith
  have y_expr_pos : 0 ≤ 1 / y ^ 2 - 1 := by unfold y; rw [sub_nonneg, div_pow, one_div_div, hl, sq_sqrt (by positivity), one_le_div (by positivity)]; nlinarith
  have z_expr_pos : 0 ≤ 1 / z ^ 2 - 1 := by unfold z; rw [sub_nonneg, div_pow, one_div_div, hl, sq_sqrt (by positivity), one_le_div (by positivity)]; nlinarith
  -- Use the key inequality
  have key_x : _ := @l_key x y z (by positivity) (by positivity) (by positivity) sum_eq_one
  have key_y : _ := @l_key y z x (by positivity) (by positivity) (by positivity) (by linarith)
  have key_z : _ := @l_key z x y (by positivity) (by positivity) (by positivity) (by linarith)
  -- Multiply the key inequalities together
  have : _ := mul_le_mul key_x key_y (by positivity) x_expr_pos
  have combined : _ := mul_le_mul this key_z (by positivity) (by nlinarith)
  -- Cancel everything out
  repeat rw [mul_rpow (by positivity) (by positivity)] at combined
  repeat rw [← rpow_mul (by positivity)] at combined
  conv_lhs at combined=> norm_num
  rw [show 8 * (x ^ (1 / 2 : ℝ) * y ^ (3 / 4 : ℝ) * z ^ (3 / 4 : ℝ)) / x ^ 2 * (8 * (y ^ (1 / 2 : ℝ) * z ^ (3 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) / y ^ 2) * (8 * (z ^ (1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) * y ^ (3 / 4 : ℝ)) / z ^ 2) = 8 * 8 * 8 * ((x ^ (1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) * x ^ (3 / 4 : ℝ)) / x ^ 2) * ((y ^ (1 / 2 : ℝ) * y ^ (3 / 4 : ℝ) * y ^ (3 / 4 : ℝ)) / y ^ 2) * ((z ^ (1 / 2 : ℝ) * z ^ (3 / 4 : ℝ) * z ^ (3 / 4 : ℝ)) / z ^ 2) by ring] at combined
  repeat rw [← rpow_add (by positivity)] at combined
  conv_lhs at combined => norm_num
  repeat rw [div_self (by positivity), mul_one] at combined
  exact combined