import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a+b+c+a b+b c+c a+a b c=7$. Prove that

$$
\sqrt{a^{2}+b^{2}+2}+\sqrt{b^{2}+c^{2}+2}+\sqrt{c^{2}+a^{2}+2} \geq 6
$$ -/
theorem inequalities_605779 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c + a * b + b * c + c * a + a * b * c = 7) :
    Real.sqrt (a ^ 2 + b ^ 2 + 2) + Real.sqrt (b ^ 2 + c ^ 2 + 2) + Real.sqrt (c ^ 2 + a ^ 2 + 2) ≥ 6 := by
  -- Show that x² + y² + 2 ≥ (x + 1)(y + 1) for all x, y.
  have h₀ (x y : ℝ) : (x + 1) * (y + 1) ≤ x ^ 2 + y ^ 2 + 2 := by
    -- This is equivalent to (x - y)² + (x - 1)² + (y - 1)² ≥ 0.
    linarith only [sq_nonneg (x - y), sq_nonneg (y - 1), sq_nonneg (x - 1)]
  -- Show that AM-GM inequality for three variables.
  have h₁ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z ≥ x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) := by
    apply Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by norm_num)
  calc
    Real.sqrt (a ^ 2 + b ^ 2 + 2) + Real.sqrt (b ^ 2 + c ^ 2 + 2) + Real.sqrt (c ^ 2 + a ^ 2 + 2)
    _ ≥ Real.sqrt ((a + 1) * (b + 1)) + Real.sqrt ((b + 1) * (c + 1)) + Real.sqrt ((c + 1) * (a + 1)) := by
      -- Apply h₀ on each term.
      apply add_le_add
      apply add_le_add
      rw [<-sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      apply h₀ a b
      rw [<-sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      apply h₀ b c
      rw [<-sq_le_sq₀ (by positivity) (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      apply h₀ c a
    _ = 3 * ((1 / 3 : ℝ) * Real.sqrt ((a + 1) * (b + 1)) + (1 / 3 : ℝ) * Real.sqrt ((b + 1) * (c + 1)) + (1 / 3 : ℝ) * Real.sqrt ((c + 1) * (a + 1))) := by
      ring
    _ ≥ 3 * (Real.sqrt ((a + 1) * (b + 1)) ^ (1 / 3 : ℝ) * Real.sqrt ((b + 1) * (c + 1)) ^ (1 / 3 : ℝ) * Real.sqrt ((c + 1) * (a + 1)) ^ (1 / 3 : ℝ)) := by
      -- Apply h₁.
      rw [ge_iff_le, mul_le_mul_left (by norm_num)]
      apply h₁
      all_goals
        positivity
    _ = 3 * (Real.sqrt ((a + 1) * (b + 1) * (c + 1) * ((a + 1) * (b + 1) * (c + 1)))) ^ (1 / 3 : ℝ) := by
      -- Simplify the expression.
      rw [<-Real.mul_rpow, <-Real.mul_rpow, <-Real.sqrt_mul, <-Real.sqrt_mul]
      ac_rfl
      all_goals
        positivity
    _ = 3 * (Real.sqrt (8 * 8)) ^ (1 / 3 : ℝ) := by
      -- Use the fact that (a + 1)(b + 1)(c + 1) induced by h.
      rw [show (a + 1) * (b + 1) * (c + 1) = 8 by linarith only [h]]
    _ = 6 := by
      simp
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, <-Real.rpow_mul]
      norm_num
      norm_num