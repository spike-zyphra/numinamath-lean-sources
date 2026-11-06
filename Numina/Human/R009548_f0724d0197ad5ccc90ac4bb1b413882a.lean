import Mathlib

/- ## T-1 A

Prove that for all positive real numbers $a, b, c$ such that $a b c=1$ the following inequality holds:


$$

\frac{a}{2 b+c^{2}}+\frac{b}{2 c+a^{2}}+\frac{c}{2 a+b^{2}} \leqslant \frac{a^{2}+b^{2}+c^{2}}{3}

$$

 -/
theorem inequalities_292056 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (2 * b + c ^ 2) + b / (2 * c + a ^ 2) + c / (2 * a + b ^ 2) ≤
    (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by
  -- first we'll prove  x / (2*y + z^2) ≤ 2/9 * x^2 + 1/9 * x which can be applied on each term
  have aux {x y z : ℝ} (hx: 0 < x) (hy: 0 < y) (hz: 0 < z) (h: x*y*z = 1) : x / (2*y + z^2) ≤ 2/9 * x^2 + 1/9 * x := by
    calc
      x / (2 * y + z^2) = x / (y + y + z^2) := by ring
      -- denominator is part of an arithmetic mean, so we can use am-gm
      _ ≤ x / (3 * (y^2)^(1/3:ℝ) * (z^2)^(1/3:ℝ)) := by
        gcongr
        have := @Real.geom_mean_le_arith_mean3_weighted (1/3:ℝ) (1/3:ℝ) (1/3:ℝ) y y (z^2) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by positivity) (by norm_num)
        rw [← Real.mul_rpow (by linarith) (by linarith), ← pow_two] at this
        rw [show y + y + z ^ 2 = 3 * (1 / 3 * y + 1 / 3 * y + 1 / 3 * z ^ 2) by ring, mul_assoc]
        gcongr
      -- replace yz as 1/x
      _ = x / (3 * ((y * z)^2)^(1/3:ℝ)) := by
        have : ((y * z)^2)^(1/3:ℝ) = (y^2)^(1/3:ℝ) * (z^2)^(1/3:ℝ) := by rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_pow]
        rw [this]
        ring
      _ = x / (3 * (((1/x)^2)^(1/3:ℝ))) := by congr 4; rw [← h]; field_simp; ring
      -- separate (x^2)^(1/3) which ispart of a geometric mean, so use am-gm again
      _ = x / 3 * (x^2)^(1/3:ℝ) := by
        field_simp
        rw [mul_comm 3, mul_assoc, ← mul_assoc _ _ 3, ← Real.mul_rpow (by positivity) (by positivity)]
        field_simp
      _ ≤ x / 3 * (x / 3 + x / 3 + 1 / 3) := by
        gcongr
        have := @Real.geom_mean_le_arith_mean3_weighted (1/3:ℝ) (1/3:ℝ) (1/3:ℝ) x x 1 (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by norm_num) (by norm_num)
        convert this using 1
        . simp
          rw [← Real.mul_rpow (by linarith) (by linarith)]
          ring_nf
        . ring
      _ = 2/9 * x^2 + 1/9 * x := by ring
  -- use the fact on each of the terms
  have h₁ : a / (2 * b + c ^ 2) + b / (2 * c + a ^ 2) + c / (2 * a + b ^ 2) ≤ 2/9 * (a^2 + b^2 + c^2) + 1/9 * (a + b + c) := by calc
    a / (2 * b + c ^ 2) + b / (2 * c + a ^ 2) + c / (2 * a + b ^ 2) ≤ (2/9 * a^2 + 1/9 * a) + (2/9 * b^2 + 1/9 * b) + (2/9 * c^2 + 1/9 * c) := by
      gcongr
      repeat exact aux (by assumption) (by assumption) (by assumption) (by linarith)
    _ = 2/9 * (a^2 + b^2 + c^2) + 1/9 * (a + b + c) := by linarith
  -- next we'll prove a + b + c ≤ a^2 + b^2 + c^2
  have h₂ : a + b + c ≤ a^2 + b^2 + c^2 := by calc
    -- mulitply 1 = (abc)^(1/3)
    a + b + c = (a + b + c) * (a^(1/3:ℝ) * b^(1/3:ℝ) * c^(1/3:ℝ)) := by
      repeat rw [← Real.mul_rpow (by positivity) (by positivity)]
      rw [habc]
      simp
    -- use am-gm to get (a+b+c)^2 / 3
    _ ≤ (a + b + c) * (1/3*a + 1/3*b + 1/3*c) := by
      gcongr
      exact @Real.geom_mean_le_arith_mean3_weighted (1/3:ℝ) (1/3:ℝ) (1/3:ℝ) a b c (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by norm_num)
    -- this is less than a^2 + b^2 + c^2 as the inequality boils down to nonegativity of sum of squares
    _ ≤ a^2 + b^2 + c^2 := by
      linarith [show (a-b)^2 + (b-c)^2 + (c-a)^2 ≥ 0 by positivity]
  -- the last two inequality prove the target
  linarith only [h₁, h₂]