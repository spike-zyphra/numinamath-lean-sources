import Mathlib

open Real

/- Let $x, y$ and $z$ be positive real numbers such that $x y z=1$. Prove that

$$
(1+x)(1+y)(1+z) \geq 2\left(1+\sqrt[3]{\frac{y}{x}}+\sqrt[3]{\frac{z}{y}}+\sqrt[3]{\frac{x}{z}}\right)
$$ -/
theorem inequalities_605477 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
(hxyz : x * y * z = 1) : (1 + x) * (1 + y) * (1 + z) ≥
2 * (1 + (y / x) ^ ((1 : ℝ) / 3) + (z / y) ^ ((1 : ℝ) / 3) + (x / z) ^ ((1 : ℝ) / 3)) := by
-- We first homogenize the inequality
  rw [ge_iff_le]; suffices homo : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
  2 * (1 + (b ^ 2 / (a * c)) ^ ((1 : ℝ) / 3) + (c ^ 2 / (a * b)) ^ ((1 : ℝ) / 3) + (a ^ 2 / (b * c)) ^ ((1 : ℝ) / 3)) ≤
  (1 + a / b) * (1 + b / c) * (1 + c / a)
  · specialize homo x 1 (1/y) hx (by norm_num) (by positivity); calc
      _ = 2 * (1 + (1 ^ 2 / (x * (1 / y))) ^ ((1:ℝ) / 3) + ((1 / y) ^ 2 / (x * 1)) ^ ((1:ℝ) / 3) + (x ^ 2 / (1 * (1 / y))) ^ ((1:ℝ) / 3)) := by
        simp; ring_nf; rw [add_assoc]; nth_rw 2 [add_assoc]; simp
        have : z * y⁻¹ = x⁻¹ * (y ^ 2)⁻¹ := by
          field_simp; rw [← mul_assoc, pow_two, ← mul_assoc]
          nth_rw 2 [mul_assoc, mul_comm]; simp [hxyz]
        rw [this]; have : x * z⁻¹ = y * x ^ 2 := by
          field_simp; rw [show y*x ^ 2*z = x*y*z*x by ring, hxyz, one_mul]
        rw [this]
      _ ≤ _ := homo
      _ = _ := by
        field_simp; simp [mul_assoc]; left; left; simp [add_mul]
        rw [← hxyz]; ring
-- To prove the homogenous inequality, we first simplify LHS of the inequality
  intro a b c apos bpos cpos; have : (b ^ 2 / (a * c)) ^ ((1:ℝ) / 3) = b / (a * b * c) ^ ((1:ℝ) / 3) := by
    rw [← mul_div_mul_left _ _ (show b≠0 by positivity), ← pow_succ']; norm_num
    rw [← rpow_natCast, div_rpow, ← rpow_mul, ← mul_assoc]; norm_num
    nth_rw 2 [mul_comm]; all_goals positivity
  rw [this]; replace this : (c ^ 2 / (a * b)) ^ ((1:ℝ) / 3) = c / (a * b * c) ^ ((1:ℝ) / 3) := by
    rw [← mul_div_mul_left _ _ (show c≠0 by positivity), ← pow_succ']; norm_num
    rw [← rpow_natCast, div_rpow, ← rpow_mul]; norm_num; rw [mul_comm]
    all_goals positivity
  rw [this]; replace this : (a ^ 2 / (b * c)) ^ ((1:ℝ) / 3) = a / (a * b * c) ^ ((1:ℝ) / 3) := by
    rw [← mul_div_mul_left _ _ (show a≠0 by positivity), ← pow_succ']; norm_num
    rw [← rpow_natCast, div_rpow, ← rpow_mul, ← mul_assoc]; norm_num
    all_goals positivity
  rw [this, add_assoc, add_assoc, div_add_div_same, div_add_div_same, show b+(c+a) = a+b+c by ring]
  rw [mul_one_add, add_comm]; calc
  -- Rearrange terms and apply AM-GM inequality approapriately
    _ ≤ 3 * ((a + b + c) / (a * b * c) ^ ((1:ℝ) / 3)) - 1 := by
      rw [← sub_nonneg, sub_sub, ← add_assoc]; nth_rw 4 [add_comm]; nth_rw 2 [add_assoc]
      rw [← sub_sub, ← sub_mul]; norm_num; rw [le_div_iff₀, ← le_div_iff₀', mul_rpow, mul_rpow]
      rw [add_div, add_div, div_eq_mul_one_div a, div_eq_mul_one_div b, div_eq_mul_one_div c]
      nth_rw 3 [mul_comm]; nth_rw 4 [mul_comm]; nth_rw 5 [mul_comm]; apply geom_mean_le_arith_mean3_weighted
      any_goals positivity
      norm_num
  -- Apply AM-GM inequality to $a⁻¹$, $b⁻¹$ and $c⁻¹$ and the goal follows
    _ ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) - 1 := by
      rw [mul_div, mul_comm, ← mul_div]; gcongr; rw [div_eq_mul_one_div, ← le_div_iff₀']
      ring_nf; rw [← rpow_neg, neg_eq_neg_one_mul, rpow_mul, rpow_neg, rpow_one, mul_inv, mul_inv]
      rw [mul_rpow, mul_rpow]; nth_rw 3 [mul_comm]; nth_rw 4 [mul_comm]; nth_rw 5 [mul_comm]
      apply geom_mean_le_arith_mean3_weighted; any_goals positivity
      norm_num
    _ = _ := by field_simp; ring