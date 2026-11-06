import Mathlib

theorem inequalities_292056 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (2 * b + c ^ 2) + b / (2 * c + a ^ 2) + c / (2 * a + b ^ 2) ≤
    (a ^ 2 + b ^ 2 + c ^ 2) / 3 := by

  have aux {x y z : ℝ} (hx: 0 < x) (hy: 0 < y) (hz: 0 < z) (h: x*y*z = 1) : x / (2*y + z^2) ≤ 2/9 * x^2 + 1/9 * x := by
    calc
      x / (2 * y + z^2) = x / (y + y + z^2) := by ring
      _ ≤ x / (3 * (y^2)^(1/3:ℝ) * (z^2)^(1/3:ℝ)) := by
        gcongr
        have := @Real.geom_mean_le_arith_mean3_weighted (1/3:ℝ) (1/3:ℝ) (1/3:ℝ) y y (z^2) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by positivity) (by norm_num)
        rw [← Real.mul_rpow (by linarith) (by linarith), ← pow_two] at this
        rw [show y + y + z ^ 2 = 3 * (1 / 3 * y + 1 / 3 * y + 1 / 3 * z ^ 2) by ring, mul_assoc]
        gcongr
      _ = x / (3 * ((y * z)^2)^(1/3:ℝ)) := by
        have : ((y * z)^2)^(1/3:ℝ) = (y^2)^(1/3:ℝ) * (z^2)^(1/3:ℝ) := by rw [← Real.mul_rpow (by positivity) (by positivity), ← mul_pow]
        rw [this]
        ring
      _ = x / (3 * (((1/x)^2)^(1/3:ℝ))) := by congr 4; rw [← h]; field_simp; ring
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

  have h₁ : a / (2 * b + c ^ 2) + b / (2 * c + a ^ 2) + c / (2 * a + b ^ 2) ≤ 2/9 * (a^2 + b^2 + c^2) + 1/9 * (a + b + c) := by calc
    a / (2 * b + c ^ 2) + b / (2 * c + a ^ 2) + c / (2 * a + b ^ 2) ≤ (2/9 * a^2 + 1/9 * a) + (2/9 * b^2 + 1/9 * b) + (2/9 * c^2 + 1/9 * c) := by
      gcongr
      repeat exact aux (by assumption) (by assumption) (by assumption) (by linarith)
    _ = 2/9 * (a^2 + b^2 + c^2) + 1/9 * (a + b + c) := by linarith

  have h₂ : a + b + c ≤ a^2 + b^2 + c^2 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  linarith [h₁, h₂]