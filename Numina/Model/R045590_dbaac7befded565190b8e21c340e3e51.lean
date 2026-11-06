import Mathlib

theorem algebra_311905 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x > y)
    (hxy1 : y * x = 1) :
    IsLeast {z | ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x > y ∧ y * x = 1 ∧ z = (3 * x ^ 3 + 125 * y ^ 3) / (x - y)} 25 := by

  constructor
  · -- We need to prove 25 is in the set.
    use Real.sqrt 5, Real.sqrt 5 / 5
    constructor
    · -- 0 < x
      positivity
    constructor
    · -- 0 < y
      have h1 : 0 < Real.sqrt 5 := by positivity
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), Real.sqrt_nonneg 5]
    constructor
    · -- x > y
      have h7 : Real.sqrt 5 > 0 := by positivity
      have h6 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.mul_self_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
    constructor
    · -- y * x = 1
      have h1 : Real.sqrt 5 > 0 := by positivity
      have h9 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
      field_simp [h9]
      <;> nlinarith
    · -- Show that the value of the expression is 25
      have h1 : Real.sqrt 5 > 0 := by positivity
      have h9 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
      have h6 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by
        calc
          Real.sqrt 5 ^ 3 = Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
          _ = 5 * Real.sqrt 5 := by rw [h9]
      have eq1 : (3 * (Real.sqrt 5) ^ 3 + 125 * (Real.sqrt 5 / 5) ^ 3) = 20 * Real.sqrt 5 := by
        nlinarith [h6, sq_nonneg (Real.sqrt 5 ^ 2 - 5), sq_nonneg (Real.sqrt 5 ^ 2), Real.sqrt_nonneg 5, sq_nonneg (Real.sqrt 5 ^ 3), Real.sqrt_nonneg (5 : ℝ)]
      have eq2 : Real.sqrt 5 - (Real.sqrt 5 / 5) = 4 * Real.sqrt 5 / 5 := by
        nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [eq1, eq2]
      have h4 : Real.sqrt 5 > 0 := by positivity
      field_simp [h4, sq (Real.sqrt 5), Real.sqrt_nonneg (5 : ℝ)]
      <;> nlinarith [sq_nonneg (Real.sqrt 5 ^ 2), sq_nonneg (Real.sqrt 5), Real.sqrt_nonneg (5 : ℝ), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)]
  · -- We need to prove 25 is the least element in the set.
    intro z h
    rcases h with ⟨x, y, hx, hy, hxy, hxy1, hz⟩
    have h1 : x - y > 0 := by
      nlinarith
    have h2 : (3 * x ^ 3 + 125 * y ^ 3) ≥ 25 * (x - y) := by
      nlinarith [sq_nonneg (x ^ 2 - 5), sq_nonneg (y ^ 2 - 1 / 5), sq_nonneg (x - Real.sqrt 5), sq_nonneg (y - Real.sqrt 5 / 5), sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x * y -1), sq_nonneg (x + y - (Real.sqrt 5 + Real.sqrt 5 / 5)), sq_nonneg (x - 5 * y), sq_nonneg (x ^ 2 - 25 * y ^ 2), hxy1, mul_pos hx hy, mul_pos hx hy]
    have h3 : (3 * x ^ 3 + 125 * y ^ 3) / (x - y) ≥ 25 := by
      have h4 : x - y > 0 := h1
      apply (le_div_iff₀ h4).mpr
      nlinarith [hxy1, mul_pos hx hy]
    nlinarith [h3, hz, mul_pos hx hy]