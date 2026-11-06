import Mathlib
/- Find the integer closest to

$$
\frac{1}{\sqrt[4]{5^{4}+1}-\sqrt[4]{5^{4}-1}}
$$ -/
set_option maxHeartbeats 400000

theorem algebra_609212 : IsMinOn ((fun x => |x - 1 / ((5 ^ 4 + 1 : ℝ) ^ ((1 : ℝ) / 4) - (5 ^ 4 - 1) ^ ((1 : ℝ) / 4))|) : ℤ → ℝ) (Set.univ : Set ℤ) 250:= by
    -- Introduce a variable `a` and hypothesis `ha`
    intro a ha
    simp
    -- Clear the hypothesis `ha` from the context
    clear ha
    field_simp
    -- Define `x` as the fourth root of (5^4 + 1)
    set x:= (5 ^ 4 + 1 : ℝ) ^ ((1 : ℝ) / 4) with hx
    set y:= (5 ^ 4 - 1 : ℝ) ^ ((1 : ℝ) / 4) with hy
    -- Prove that `x` is greater than `y`
    have hxy : x > y:= by
      have g1 : 5 ^ 4 + (1 : ℝ) > 5 ^ 4 - (1 : ℝ):= by linarith
      -- Use the property of real powers to conclude `x > y`
      refine (Real.rpow_lt_rpow_iff (by linarith) (by linarith) (by linarith)).mpr g1
    have h1 : x ^ 4 = 5 ^ 4 + 1:= by
      rw [show x ^ 4 = x ^ (4 : ℝ) by norm_cast]
      -- Substitute the definition of `x`
      rw [hx]
      rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 4) 4)]
      ring_nf
    -- Prove that `y^4` equals 5^4 - 1
    have h2 : y ^ 4 = 5 ^ 4 - 1:= by
      -- Show that `y^4` is equivalent to `y` raised to the power of 4
      rw [show y ^ 4 = y ^ (4 : ℝ) by norm_cast]
      rw [hy]
      rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 4) 4)]
      ring_nf
    -- Prove that `x` is positive
    have hxpos : x > 0:= by
      rw [hx]
      -- Use positivity to conclude `x > 0`
      positivity
    -- Prove that `y` is positive
    have hypos : y > 0:= by
      rw [hy]
      positivity
    -- Prove the expression for `1 / (x - y)`
    have h3 : 1 / (x - y) = (x + y) * (x ^ 2 + y ^ 2) / 2:= by
      -- Show that `x - y` is positive
      replace hxy : x - y > 0:= by linarith
      -- Simplify expressions involving fields
      field_simp
      ring_nf
      -- Use linear arithmetic to conclude
      linarith
    have g1 : x > 5:= by
      -- Assume the contrary
      by_contra H
      simp at H
      -- Show that `5 - x` is non-negative
      replace H : 5 - x ≥ 0:= by linarith
      have g3 : (5 - x) * (x + 5) * (x ^ 2 + 5 ^ 2) ≥ 0:= by positivity
      -- Conclude the contradiction
      linarith
    have g2 : y > 4:= by
      -- Assume the contrary
      by_contra H
      simp at H
      -- Show that `4 - y` is non-negative
      replace H : 4 - y ≥ 0:= by linarith
      have g3 : (4 - y) * (y + 4) * (y ^ 2 + 4 ^ 2) ≥ 0:= by positivity
      linarith
    -- Prove that `x - 5` is less than 1/500
    have g3 : x - 5 < 1 / 500:= by
      -- Express `x - 5` in terms of a fraction
      rw [show x - 5 = 1 / ((x + 5) * (x ^ 2 + 5 ^ 2)) by field_simp ; linarith]
      have g5 : x ^ 2 + 5 ^ 2 > 50:= by
        -- Show that `(x - 5) * (x + 5)` is positive
        have g6 : (x - 5) * (x + 5) > 0:= by
          -- Prove that `x - 5` is positive
          replace g1 : x - 5 > 0:= by linarith
          positivity
        linarith
      -- Prove that `(x + 5) * (x^2 + 5^2)` is greater than 500
      have g6 : (x + 5) * (x ^ 2 + 5 ^ 2) > 10 * 50:= by refine mul_lt_mul_of_nonneg_of_pos' (by linarith) g5 (by linarith) (by linarith)
      -- Simplify the expression
      rw [show (10 : ℝ) * 50 = 500 by ring_nf] at g6
      refine one_div_lt_one_div_of_lt (by linarith) g6
    have g4 : 5 - y < 1 / 256:= by
      rw [show 5 - y = 1 / ((y + 5) * (y ^ 2 + 5 ^ 2)) by field_simp ; linarith]
      -- Prove that `y^2 + 5^2` is greater than 32
      have g5 : y ^ 2 + 5 ^ 2 > 32:= by
        -- Show that `(y - 4) * (y + 4)` is positive
        have g6 : (y - 4) * (y + 4) > 0:= by
          replace g2 : y - 4 > 0:= by linarith
          positivity
        linarith
      -- Prove that `(y + 5) * (y^2 + 5^2)` is greater than 256
      have g6 : (y + 5) * (y ^ 2 + 5 ^ 2) > 8 * 32:= by refine mul_lt_mul_of_nonneg_of_pos' (by linarith) g5 (by linarith) (by linarith)
      -- Simplify the expression
      rw [show (8 : ℝ) * 32 = 256 by ring_nf] at g6
      refine one_div_lt_one_div_of_lt (by linarith) g6
    have g5 : x ^ 2 - 5 ^ 2 < 1 / 50:= by
      rw [show x ^ 2 - 5 ^ 2 = 1 / (x ^ 2 + 5 ^ 2) by field_simp ; linarith]
      have g6 : x ^ 2 + 5 ^ 2 > 50:= by
        have g7 : (x - 5) * (x + 5) > 0:= by
          -- Prove that `x - 5` is positive
          replace g1 : x - 5 > 0:= by linarith
          -- Use positivity to conclude
          positivity
        linarith
      -- Use the property of reciprocals to conclude
      apply one_div_lt_one_div_of_lt (by linarith) g6
    have g6 : 5 ^ 2 - y ^ 2 < 1 / 45:= by
      rw [show 5 ^ 2 - y ^ 2 = 1 / (y ^ 2 + 5 ^ 2) by field_simp ; linarith]
      have g7 : y ^ 2 > (9 / 2) ^ 2:= by
        -- Assume the contrary
        by_contra H
        simp at H
        -- Show that `(9/2)^2 - y^2` is non-negative
        replace H : (9 / 2) ^ 2 - y ^ 2 ≥ 0:= by linarith
        replace H : ((9 / 2) ^ 2 - y ^ 2) * (y ^ 2 + (9 / 2) ^ 2) ≥ 0:= by positivity
        -- Conclude the contradiction
        linarith
      -- Prove that `y^2 + 5^2` is greater than 45
      replace g7 : y ^ 2 + 5 ^ 2 > 45:= by linarith
      apply one_div_lt_one_div_of_lt (by linarith) g7
    replace g2 : y < 5:= by
      by_contra H
      -- Simplify the assumption
      simp at H
      replace H : y - 5 ≥ 0:= by linarith
      replace H : ((y - 5) * (y + 5) * (y ^ 2 + 5 ^ 2)) ≥ 0:= by positivity
      -- Conclude the contradiction
      linarith
    -- Prove that the absolute value of (x + y - 10) is less than 1/256
    have g7 : |x + y - 10| < 1 / 256:= by
      rw [show x + y - 10 = (x - 5) - (5 - y) by ring_nf]
      have g8 : |(x - 5) - (5 - y)| ≤ max |x - 5| |5 - y|:= by
        by_cases g9 : (x - 5) - (5 - y) ≥ 0
        .
          rw [abs_of_nonneg (by linarith)]
          -- Prove that the maximum of |x - 5| and |5 - y| is greater than or equal to |x - 5|
          have g10 : max |x - 5| |5 - y| ≥ |x - 5|:= by exact le_max_left |x - 5| |5 - y|
          have g11 : |x - 5| ≥ x - 5:= by exact le_abs_self (x - 5)
          linarith
        .
          simp at g9
          rw [abs_of_nonpos (by linarith)]
          -- Prove that the maximum of |x - 5| and |5 - y| is greater than or equal to |5 - y|
          have g10 : max |x - 5| |5 - y| ≥ |5 - y|:= by exact le_max_right |x - 5| |5 - y|
          -- Prove that |5 - y| is greater than or equal to 5 - y
          have g11 : |5 - y| ≥ 5 - y:= by exact le_abs_self (5 - y)
          linarith
      rw [show |x - 5| = x - 5 by exact abs_of_nonneg (by linarith)] at g8
      rw [show |5 - y| = 5 - y by exact abs_of_nonneg (by linarith)] at g8
      -- Use the property of absolute value subtraction to conclude
      refine abs_sub_lt_of_nonneg_of_lt (by linarith) (by linarith) (by linarith) g4
    -- Prove that the absolute value of (x^2 + y^2 - 50) is less than 1/45
    have g8 : |x ^ 2 + y ^ 2 - 50| < 1 / 45:= by
      rw [show x ^ 2 + y ^ 2 - 50 = (x ^ 2 - 5 ^ 2) - (5 ^ 2 - y ^ 2) by ring_nf]
      have g9 : |(x ^ 2 - 5 ^ 2) - (5 ^ 2 - y ^ 2)| ≤ max |x ^ 2 - 5 ^ 2| |5 ^ 2 - y ^ 2|:= by
        -- Consider the case where (x^2 - 5^2) - (5^2 - y^2) is non-negative
        by_cases g10 : (x ^ 2 - 5 ^ 2) - (5 ^ 2 - y ^ 2) ≥ 0
        .
          -- Use the property of absolute value for non-negative numbers
          rw [abs_of_nonneg (by linarith)]
          have g11 : max |x ^ 2 - 5 ^ 2| |5 ^ 2 - y ^ 2| ≥ |x ^ 2 - 5 ^ 2|:= by exact le_max_left |x ^ 2 - 5 ^ 2| |5 ^ 2 - y ^ 2|
          have g12 : |x ^ 2 - 5 ^ 2| ≥ x ^ 2 - 5 ^ 2:= by exact le_abs_self (x ^ 2 - 5 ^ 2)
          -- Prove that 5 - y is positive
          replace g2 : 5 - y > 0:= by linarith
          -- Prove that (5 - y) * (5 + y) is positive
          replace g2 : (5 - y) * (5 + y) > 0:= by positivity
          linarith
        .
          simp at g10
          rw [abs_of_nonpos (by linarith)]
          -- Prove that the maximum of |x^2 - 5^2| and |5^2 - y^2| is greater than or equal to |5^2 - y^2|
          have g11 : max |x ^ 2 - 5 ^ 2| |5 ^ 2 - y ^ 2| ≥ |5 ^ 2 - y ^ 2|:= by exact le_max_right |x ^ 2 - 5 ^ 2| |5 ^ 2 - y ^ 2|
          -- Prove that |5^2 - y^2| is greater than or equal to 5^2 - y^2
          have g12 : |5 ^ 2 - y ^ 2| ≥ 5 ^ 2 - y ^ 2:= by exact le_abs_self (5 ^ 2 - y ^ 2)
          replace g1 : x - 5 > 0:= by linarith
          replace g1 : (x - 5) * (x + 5) > 0:= by positivity
          linarith
      -- Rewrite |x^2 - 5^2| as x^2 - 5^2 using the property of absolute value for non-negative numbers
      rw [show |x ^ 2 - 5 ^ 2| = x ^ 2 - 5 ^ 2 by exact abs_of_nonneg (by nlinarith only [g1])] at g9
      -- Prove that 5 - y is positive
      replace g2 : 5 - y > 0:= by linarith
      rw [show |5 ^ 2 - y ^ 2| = 5 ^ 2 - y ^ 2 by exact abs_of_nonneg (by linarith only [show (5 - y) * (5 + y) ≥ 0 by positivity])] at g9
      refine abs_sub_lt_of_nonneg_of_lt (by nlinarith only [g1]) (by linarith) (by linarith only [show (5 - y) * (5 + y) ≥ 0 by positivity]) g6
    -- Prove that the absolute value of (250 - 1 / (x - y)) is less than 1/2
    have g9 : |250 - 1 / (x - y)| < 1 / 2:= by
      -- Rewrite 250 - 1 / (x - y) using the expression for 1 / (x - y)
      rw [show 250 - 1 / (x - y) = -((1 / 2) * ((x + y - 10) * (x ^ 2 + y ^ 2 - 50) + 10 * (x ^ 2 + y ^ 2 - 50) + 50 * (x + y - 10))) by rw [h3] ; ring_nf]
      rw [abs_neg _]
      rw [abs_mul (1 / 2) _]
      -- Simplify the absolute value of 1/2
      rw [show |(1 : ℝ) / 2| = 1 / 2 by simp]
      -- Use the triangle inequality for absolute values
      have g9 := abs_add_le ((x + y - 10) * (x ^ 2 + y ^ 2 - 50) + 10 * (x ^ 2 + y ^ 2 - 50)) (50 * (x + y - 10))
      have g10 := abs_add_le ((x + y - 10) * (x ^ 2 + y ^ 2 - 50)) (10 * (x ^ 2 + y ^ 2 - 50))
      rw [abs_mul (x + y - 10) (x ^ 2 + y ^ 2 - 50)] at g10
      -- Use the property of absolute value for multiplication
      rw [abs_mul 10 (x ^ 2 + y ^ 2 - 50)] at g10
      -- Use the property of absolute value for multiplication
      rw [abs_mul 50 (x + y - 10)] at g9
      rw [show |(10 : ℝ)| = 10 by simp] at g10
      rw [show |(50 : ℝ)| = 50 by simp] at g9
      -- Prove that the product of |x + y - 10| and |x^2 + y^2 - 50| is less than 1/256 * 1/45
      have g11 : |x + y - 10| * |x ^ 2 + y ^ 2 - 50| < 1 / 256 * (1 / 45):= by refine mul_lt_mul_of_nonneg_of_pos' (by linarith) g8 (by positivity) (by linarith)
      -- Clear unnecessary hypotheses and values
      clear g1 g2 g3 g4 g5 g6 h1 h2 hxpos hypos hxy hx hy h3
      clear_value x y
      set b:= (x + y - 10) * (x ^ 2 + y ^ 2 - 50) + 10 * (x ^ 2 + y ^ 2 - 50) + 50 * (x + y - 10) with hb
      set c:= (x + y - 10) * (x ^ 2 + y ^ 2 - 50) + 10 * (x ^ 2 + y ^ 2 - 50) with hc
      set d:= x + y - 10 with hd
      set e:= x ^ 2 + y ^ 2 - 50 with he
      replace g10 : |c| < 1 / 256 * (1 / 45) + 10 * (1 / 45):= by linarith
      -- Prove that the absolute value of b is less than 1/256 * 1/45 + 10 * 1/45 + 50 * 1/256
      replace g9 : |b| < 1 / 256 * (1 / 45) + 10 * (1 / 45) + 50 * (1 / 256):= by linarith
      -- Clear unnecessary values
      clear_value b c d e
      norm_num at g9
      linarith
    clear g1 g2 g3 g4 g5 g6 h1 h2 hxpos hypos hxy hx hy h3 g7 g8
    clear_value x y
    -- Consider the case where a equals 250
    by_cases ha : a = 250
    .
      -- Substitute a with 250
      subst a
      simp
    .
      replace ha : a - 250 ≠ 0:= by exact sub_ne_zero_of_ne ha
      -- Prove that the absolute value of a - 250 is positive
      replace ha : |a - 250| > 0:= by positivity
      -- Prove that the absolute value of a - 250 is greater than or equal to 1
      replace ha : |a - 250| ≥ 1:= by linarith
      rify at ha
      rw [show ↑a - 1 / (x - y) = ↑a - 250 + (250 - 1 / (x - y)) by ring]
      -- Use the triangle inequality for absolute values
      have h1 : |↑a - 250 + (250 - 1 / (x - y))| + |-(250 - 1 / (x - y))| ≥ |↑a - 250 + (250 - 1 / (x - y)) + -(250 - 1 / (x - y))|:= by exact abs_add_le (↑a - 250 + (250 - 1 / (x - y))) (-(250 - 1 / (x - y)))
      -- Use the property of absolute value for negative numbers
      rw [abs_neg _] at h1
      rw [show ↑a - 250 + (250 - 1 / (x - y)) + -(250 - 1 / (x - y)) = ↑a - 250 by linarith] at h1
      linarith
