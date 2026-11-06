import Mathlib


theorem algebra_12712 {f:ℝ → ℝ → ℝ}
    (hf: f = fun a b => 1/a + 1/b) :
    IsLeast {x| ∃a b:ℝ, (x = (f a b) ∧  0 < a ∧ 0 < b ∧ a+2*b=1)} (3+2*√2) := by
  constructor
  · -- Show that 3 + 2*sqrt 2 is in the set.
    use Real.sqrt 2 - 1, (2 - Real.sqrt 2) / 2
    constructor
    · -- Show that (3 + 2*√2) = f (a, b).
      rw [hf]
      have h1 : Real.sqrt 2 > 1 := by
        have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
        linarith
      have h2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2)]
      have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h4 : 1 / (Real.sqrt 2 - 1) = Real.sqrt 2 + 1 := by
        have h7 : Real.sqrt 2 - 1 ≠ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), h1]
        field_simp [h7]
        nlinarith [h3]
      have h5 : 1 / ((2 - Real.sqrt 2) / 2) = 2 + Real.sqrt 2 := by
        have h7 : (2 - Real.sqrt 2) ≠ 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), h2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
        field_simp [h7]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
      simp [h4, h5]
      all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
    constructor
    · -- Show that 0 < a.
      have h1 : Real.sqrt 2 > 1 := by
        have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
        linarith
      have h3 : 0 < Real.sqrt 2 - 1 := by linarith
      linarith
    constructor
    · -- Show that 0 < b.
      have h2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
      have h4 : (2 - Real.sqrt 2) > 0 := by nlinarith
      have h5 : (2 - Real.sqrt 2) / 2 > 0 := by linarith
      linarith
    · -- Show that a + 2 * b = 1.
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]
  · -- Show that 3 + 2*sqrt 2 is the minimum.
    intro x hx
    rcases hx with ⟨a, b, h_eq, ha_pos, hb_pos, h_eq1⟩
    rw [hf] at h_eq
    have h1 : 0 < a := by linarith
    have h2 : 0 < b := by linarith
    have h3 : a + 2 * b = 1 := h_eq1
    have h4 : 1 / a + 1 / b ≥ 3 + 2 * Real.sqrt 2 := by
      have h5 : 0 < a := by linarith
      have h6 : 0 < b := by linarith
      have h7 : 1 / a + 1 / b - (3 + 2 * Real.sqrt 2) ≥ 0 := by
        have h8 : 0 < a * b := mul_pos ha_pos hb_pos
        have h9 : (1 / a + 1 / b - (3 + 2 * Real.sqrt 2)) = (a + b - (3 + 2 * Real.sqrt 2) * (a * b)) / (a * b) := by
          field_simp
          nlinarith
        rw [h9]
        have h10 : a + b - (3 + 2 * Real.sqrt 2) * (a * b) ≥ 0 := by
          nlinarith [sq_nonneg (a - (Real.sqrt 2 - 1)), sq_nonneg (b - (2 - Real.sqrt 2) / 2), 
            sq_nonneg (a * b), sq_nonneg (a + 2 * b - 1), 
            mul_pos ha_pos hb_pos, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2), 
            sq_nonneg (Real.sqrt 2 ^ 2 - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0)]
        have h11 : (a * b) > 0 := mul_pos ha_pos hb_pos
        apply div_nonneg
        linarith
        positivity
      linarith
    have h9 : x = 1 / a + 1 / b := by
      simp [h_eq]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num : (0 : ℝ) ≤ 2)]