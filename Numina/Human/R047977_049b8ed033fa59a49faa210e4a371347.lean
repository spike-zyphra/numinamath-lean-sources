import Mathlib

open Real

/- 9th Putnam 1949 Problem B1 Show that for any rational a/b ∈ (0, 1), we have |a/b - 1/√2| > 1/(4b 2 ). -/
theorem number_theory_149531 {a b : ℤ} (hab : 0 < a ∧ a < b) :
    |(a / b : ℝ) - 1 / √2| > 1 / (4 * b ^ 2) := by
  -- suppose that |a / b - 1 / √2| ≤ 1 / (4 * b ^ 2)
  by_contra! h
  have hb : 0 < b := by linarith
  have hb2 : 0 < (2 : ℝ) * b ^ 2 := by positivity
  -- 1 / √2 is irrational so a / b ≠ 1 / √2 and |a / b - 1 / √2| > 0
  have ineq1 : (a / b : ℝ) ≠ 1 / √2 := by
    suffices Irrational (1 / √2) by
      rw [irrational_iff_ne_rational] at this
      exact (this a b).symm
    norm_num
    exact irrational_sqrt_two
  -- prove that |2 * a ^ 2 - b ^ 2| / (2 * b ^ 2) < 1 / (2 * b ^ 2)
  have ineq2 : |(2 : ℝ) * a ^ 2 - b ^ 2| / (2 * b ^ 2) < 1 / (2 * b ^ 2) := calc
    _ = |(a / b : ℝ) - 1 / √2| * |a / b + 1 / √2| := by
          rw [←abs_mul]
          nth_rw 3 [mul_comm]
          rw [←sq_sub_sq]
          norm_num
          field_simp
          have : (2 : ℝ) * b ^ 2 = |(2 : ℝ) * b ^ 2| := by rw [abs_of_nonneg (le_of_lt hb2)]
          rw [this, ←abs_mul, mul_comm ((b : ℝ) ^ 2), div_mul_cancel₀ _ (ne_of_gt hb2), mul_comm]
    -- we have |a / b + 1 / √2| ≤ a / b + 1 / √2 < 1 + 1 = 2
    _ < |(a / b : ℝ) - 1 / √2| * 2 := by
          apply mul_lt_mul' (le_refl _) _ (abs_nonneg _)
          · rw [abs_pos]
            contrapose! ineq1
            linarith
          · apply lt_of_le_of_lt (abs_add_le _ _)
            nth_rw 2 [show (2 : ℝ) = 1 + 1 by norm_num]
            apply add_lt_add
            · rify at hb hab
              rw [abs_of_nonneg, div_lt_one hb]
              exact hab.2
              apply le_of_lt
              exact div_pos hab.1 hb
            · rw [abs_of_nonneg (by norm_num)]
              rw [div_lt_one (by norm_num)]
              rw [show (1 : ℝ) = √1 by norm_num]
              exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    _ ≤ 1 / (4 * b ^ 2) * 2 := by linarith
    _ = 1 / (2 * b ^ 2) := by
          field_simp
          ring
  -- we get |2 * a ^ 2 - b ^ 2| < 1
  have ineq3 : |2 * a ^ 2 - b ^ 2| < 1 := by
    rify
    rw [div_lt_div_iff_of_pos_right hb2] at ineq2
    exact ineq2
  -- we derive that 2 * a ^ 2 = b ^ 2 and so 2 = (b / a) ^ 2
  have eq : 2 = ((b : ℝ) / a) ^ 2 := by
    have : (a : ℝ) ^ 2 ≠ 0 := by
      rify at hab
      nlinarith
    field_simp [this]
    norm_cast
    rw [abs_lt] at ineq3
    omega
  -- √2 is irrational so 2 = (b / a)^2 is impossible
  have hirr : Irrational √(2 : ℚ) := by
    norm_cast
    exact irrational_sqrt_two
  rw [irrational_sqrt_ratCast_iff, IsSquare] at hirr
  replace hirr := hirr.1
  contrapose! hirr
  use b / a
  rify
  rw [eq, pow_two]