import Mathlib

/- Laat $a, b$ en $c$ positieve reële getallen zijn die voldoen aan $a+b+c \geq a b c$. Bewijs dat

$$
a^{2}+b^{2}+c^{2} \geq \sqrt{3} a b c
$$ -/
theorem inequalities_606277 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c ≥ a * b * c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ Real.sqrt 3 * a * b * c := by
  -- First show that a² + b² + c² ≥ 3(abc)^(2 / 3).
  have h₀ : a ^ 2 + b ^ 2 + c ^ 2 ≥ 3 * (a * b * c) ^ (2 / 3 : ℝ) := by
    calc
      a ^ 2 + b ^ 2 + c ^ 2 ≥ (a + b + c) ^ 2 / 3 := by
        -- This inequality is equivalent to (a - b)² + (b - c)² + (c - a)² ≥ 0.
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      _ ≥ 3 * (a * b * c) ^ (2 / 3 : ℝ) := by
        -- Take square root of both sides to change the inequality to a + b + c ≥ 3(abc)^(1 / 3).
        rw [ge_iff_le, le_div_iff₀ (by positivity), div_eq_mul_one_div, mul_comm, mul_comm 2 (1 / 3), Real.rpow_mul (by positivity), <-mul_assoc, <-pow_two, show (2 : ℝ) = (2 : ℕ) by simp, Real.rpow_natCast, <-mul_pow, sq_le_sq₀ (by positivity) (by positivity)]
        -- Change the inequality to a suitable form to apply weighted AM-GM inequality.
        rw [mul_comm, <-le_div_iff₀ (by positivity), Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity), add_div, add_div, div_eq_mul_one_div a, div_eq_mul_one_div b, div_eq_mul_one_div c, mul_comm a (1 / 3), mul_comm b (1 / 3), mul_comm c (1 / 3)]
        -- Apply AM-GM inequality of three variables.
        apply Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity) (by positivity) (by norm_num)
  -- Also show that a² + b² + c² ≥ (abc)² / 3.
  have h₁ : a ^ 2 + b ^ 2 + c ^ 2 ≥ (a * b * c) ^ 2 / 3 := by
    calc
      a ^ 2 + b ^ 2 + c ^ 2 ≥ (a + b + c) ^ 2 / 3 := by
        -- This inequality is equivalent to (a - b)² + (b - c)² + (c - a)² ≥ 0.
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      _ ≥ (a * b * c) ^ 2 / 3 := by
        -- Use the given inequality a + b + c ≥ abc.
        rw [ge_iff_le, div_le_div_iff_of_pos_right (by norm_num), sq_le_sq₀ (by positivity) (by positivity)]
        simp [h]
  -- Raise the first inequality to the power of 3 / 4 and the second to the power of 1 / 4 to get the desired result.
  calc
    a ^ 2 + b ^ 2 + c ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) ^ (3 / 4 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2) ^ (1 / 4 : ℝ) := by
      rw [<-Real.rpow_add (by positivity)]
      norm_num
    _ ≥ (3 * (a * b * c) ^ (2 / 3 : ℝ)) ^ (3 / 4 : ℝ) * ((a * b * c) ^ 2 / 3) ^ (1 / 4 : ℝ) := by
      -- Use h₀ and h₁ proved above.
      apply mul_le_mul
      apply Real.rpow_le_rpow (by positivity) h₀ (by norm_num)
      apply Real.rpow_le_rpow (by positivity) h₁ (by norm_num)
      positivity
      positivity
    _ = 3 ^ (1 / 2 : ℝ) * (a * b * c) := by
      -- Performing some tedious simplification to get the equality.
      rw [Real.mul_rpow, mul_assoc, <-Real.rpow_mul, Real.div_rpow, show (a * b * c) ^ 2 = (a * b * c) ^ (2 : ℝ) by rw [<-Real.rpow_natCast]; simp, <-Real.rpow_mul, <-mul_div_assoc]
      norm_num
      rw [<-Real.mul_rpow, <-pow_two, show (a * b * c) ^ 2 = (a * b * c) ^ (2 : ℝ) by rw [<-Real.rpow_natCast]; simp, <-Real.rpow_mul]
      norm_num
      rw [<-mul_div_assoc, mul_comm, mul_div_assoc, mul_comm, <-Real.rpow_sub]
      norm_num
      all_goals
        positivity
    _ = Real.sqrt 3 * a * b * c := by
      -- Simplify the expression to get the desired result.
      rw [Real.sqrt_eq_rpow]
      ring_nf
      