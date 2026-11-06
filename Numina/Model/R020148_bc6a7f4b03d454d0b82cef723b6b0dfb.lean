import Mathlib

theorem algebra_309806 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≥ y)
    (h : ∃ a b, 0 ≤ a ∧ a ≤ x ∧ 0 ≤ b ∧ b ≤ y ∧ (x - a)^2 + (y - b)^2 = x^2 + b^2 ∧
      x^2 + b^2 = y^2 + a^2) :
    x / y ≤ 2 * Real.sqrt 3 / 3 := by
  rcases h with ⟨a, b, ha1, ha2, hb1, hb2, heq1, heq2⟩
  have eq1 : y ^ 2 - 2 * a * x - 2 * b * y + a ^ 2 = 0 := by
    nlinarith
  have eq2 : x ^ 2 + b ^ 2 = y ^ 2 + a ^ 2 := by
    nlinarith
  have h1 : (x / y) ^ 2 ≤ (4 / 3) := by
    have pos1 : 0 < y := hy
    have pos2 : 0 < y ^ 2 := by
      nlinarith
    have h' : x ^ 2 / y ^ 2 ≤ (4 / 3 : ℝ) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (x - 2 * y * Real.sqrt 3 / 3), sq_nonneg (y - x * Real.sqrt 3 / 2), 
          sq_nonneg (a - (Real.sqrt 3 / 3) * y), sq_nonneg (b - (Real.sqrt 3 / 3) * x), 
          Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
          mul_pos hx hy, mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
          sq_nonneg (x^2 + b^2 - y^2 - a^2), sq_nonneg (y^2 - 2 * a * x - 2 * b * y + a^2), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)]
    have : (x / y) ^ 2 = x ^ 2 / y ^ 2 := by
      field_simp
    nlinarith
  have h2 : x / y ≤ 2 * Real.sqrt 3 / 3 := by
    have h11 : (x / y) ^ 2 ≤ (4 / 3) := h1
    have h40 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num)
    have h44 : (2 * Real.sqrt 3 / 3) ^ 2 = (4 / 3) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h'5 : x / y ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    have h'6 : (x / y) ≤ Real.sqrt (4 / 3) := by
      apply Real.le_sqrt_of_sq_le
      linarith
    have h'7 : Real.sqrt (4 / 3) = (2 * Real.sqrt 3 / 3) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (2 * Real.sqrt 3 / 3 - (Real.sqrt 3 * 2 / 3) ) ]
    linarith [Real.sqrt_nonneg (4/3), h'7]
  exact h2