import Mathlib

/- Montrer que si $a, b, c$ sont des nombres réels positifs vérifiant $a+b+c=1$ alors

$$
\frac{7+2 b}{1+a}+\frac{7+2 c}{1+b}+\frac{7+2 a}{1+c} \geqslant \frac{69}{4}
$$ -/
theorem inequalities_605087 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
    (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) ≥ 69 / 4 := by
  -- Prove the AM-GM inequality for three variables.
  have AM_GM_ineq (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z ≥ x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) := by
    apply Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by norm_num)
  -- Prove the AM-HM inequality for three variables.
  have AM_HM_ineq (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 1 / x + 1 / y + 1 / z ≥ 9 / (x + y + z) := by
    -- Apply the AM-GM inequality for x, y, z and for 1/x, 1/y, 1/z respectively.
    have h₀ := AM_GM_ineq x y z hx hy hz
    have h₁ := AM_GM_ineq (1 / x) (1 / y) (1 / z) (by positivity) (by positivity) (by positivity)
    -- Combine these two inequalities together.
    calc
      1 / x + 1 / y + 1 / z
      _ = 3 * ((1 / 3) * (1 / x) + (1 / 3) * (1 / y) + (1 / 3) * (1 / z)) := by ring
      _ ≥ 3 * ((1 / x) ^ (1 / 3 : ℝ) * (1 / y) ^ (1 / 3 : ℝ) * (1 / z) ^ (1 / 3 : ℝ)) := by
        -- Apply h₁ first.
        rw [ge_iff_le, mul_le_mul_left (by norm_num)]
        apply h₁
      _ = 3 / (x * y * z) ^ (1 / 3 : ℝ) := by
        -- Simplify the expression as inverse of GM.
        rw [Real.mul_rpow, Real.mul_rpow, one_div x, one_div y, one_div z]
        iterate 3 rw [Real.inv_rpow, <-one_div]
        rw [one_div_mul_one_div, one_div_mul_one_div, <-mul_div_assoc]
        norm_num
        all_goals
          positivity
      _ ≥ 3 / ((x + y + z) / 3) := by
        -- Apply h₀ next.
        rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity), mul_le_mul_left (by norm_num), <-ge_iff_le, div_eq_mul_one_div _ 3, mul_comm]
        iterate 2 rw [mul_add, Real.mul_rpow (by positivity) (by positivity)]
        apply h₀
      _ = 9 / (x + y + z) := by
        -- Simplify the expression.
        rw [div_div_eq_mul_div]
        norm_num
  -- Prove the desired inequality in separated steps.
  calc
    (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c)
    _ = 5 * (1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)) + 2 * ((1 + b) / (1 + a) + (1 + c) / (1 + b) + (1 + a) / (1 + c)) := by
      -- The left-hand-side could be changed to 5(1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)) + 2((1 + b) / (1 + a) + (1 + c) / (1 + b) + (1 + a) / (1 + c)).
      ring
    _ ≥ 5 * (9 / 4) + 2 * 3 := by
      -- Bound the first term below by 5 * (9 / 4) and second by 2 * 3.
      apply add_le_add
      . -- Manipulate the first term.
        rw [mul_le_mul_left (by norm_num)]
        -- Use the fact that 4 = (1 + a) + (1 + b) + (1 + c).
        rw [show (4 : ℝ) = (1 + a) + (1 + b) + (1 + c) by linarith only [h]]
        -- Apply AM_HM_ineq.
        apply AM_HM_ineq
        all_goals
          positivity
      . -- Manipulate the second term.
        rw [mul_le_mul_left (by norm_num)]
        -- Use AM_GM_ineq.
        have h₀ := AM_GM_ineq ((1 + b) / (1 + a)) ((1 + c) / (1 + b)) ((1 + a) / (1 + c)) (by positivity) (by positivity) (by positivity)
        -- Simplify the expression.
        iterate 2 rw [<-mul_add, <-Real.mul_rpow (by positivity) (by positivity)] at h₀
        iterate 2 rw [div_mul_div_comm] at h₀
        rw [show (1 + b) * (1 + c) * (1 + a) = (1 + a) * (1 + b) * (1 + c) by ring, div_self (by positivity), Real.one_rpow] at h₀
        rw [mul_comm, mul_one_div, ge_iff_le, le_div_iff₀ (by norm_num)] at h₀
        norm_num at h₀
        apply h₀
    _ = 69 / 4 := by
      -- Simplify the expression.
      norm_num
