import Mathlib

/- 4. For positive numbers $a, b$ and $c$, prove the inequality

$$
1+\frac{3}{a b+b c+c a} \geqslant \frac{6}{a+b+c} .
$$ -/
theorem inequalities_224703 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by

    -- step 1 : we show that (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)
    -- this is done by expanding the square, and use the inequality x ^ 2 + y ^ 2 ≥ 2 * x * y
    have three_sum_sq : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
      calc
        (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b + 2 * b * c + 2 * c * a := by ring
        _ = ((a ^ 2 + b ^ 2) + (b ^ 2 + c ^ 2) + (c ^ 2 + a ^ 2)) / 2 + 2 * a * b + 2 * b * c + 2 * c * a := by ring
        _ ≥ (2 * a * b + 2 * b * c + 2 * c * a) / 2 + 2 * a * b + 2 * b * c + 2 * c * a := by rel [two_mul_le_add_sq a b, two_mul_le_add_sq b c, two_mul_le_add_sq c a]
        _ = 3 * (a * b + b * c + c * a) := by ring

    -- some auxiliary facts, will be used by `linarith`
    have : a * b > 0 := mul_pos ha hb
    have : b * c > 0 := mul_pos hb hc
    have : c * a > 0 := mul_pos hc ha

    -- step 2, we bound LHS by 1 + 9 / ((a + b + c) ^ 2),
    -- write this as a sum of two squares, then apply AM-GM inequality.
    calc
      1 + 3 / (a * b + b * c + c * a) = 1 + 9 / (3 * (a * b + b * c + c * a)) := by
        simp; apply (div_eq_div_iff ?_ ?_).mpr; ring; all_goals linarith
      _ ≥ 1 + 9 / ((a + b + c) ^ 2) := by rel [three_sum_sq]
      _ = 1 ^ 2 + (3 / (a + b + c)) ^ 2 := by field_simp; norm_num
      _ ≥ 2 * 1 * (3 / (a + b + c)) := two_mul_le_add_sq 1 (3 / (a + b + c))
      _ = _ := by ring
