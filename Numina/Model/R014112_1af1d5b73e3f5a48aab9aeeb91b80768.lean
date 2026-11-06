import Mathlib

open BigOperators Real Set

theorem inequalities_250608 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = (4 * a * c + b * c) / (a ^ 2 + b ^ 2 + c ^ 2)} (Real.sqrt 17 / 2) := by
  constructor
  · -- First part: show that sqrt(17)/2 is in the set.
    use 4, 1, Real.sqrt 17
    constructor
    · norm_num  -- a > 0
    constructor
    · norm_num  -- b > 0
    constructor
    · -- Show that sqrt 17 > 0
      have h17 : Real.sqrt 17 > 0 := by
        apply Real.sqrt_pos.mpr
        all_goals norm_num
      linarith
    · -- Show that sqrt(17)/2 = (4 * a * c + b * c) / (a ^ 2 + b ^ 2 + c ^ 2)
      have h17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
      field_simp [h17]
      <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (17 : ℝ) > 0), Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)]
  · -- Second part: show that sqrt(17)/2 is the greatest element
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq⟩
    have h1 : (4 * a * c + b * c) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ Real.sqrt 17 / 2 := by
      have h2 : a ^ 2 + b ^ 2 + c ^ 2 > 0 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
      have h3 : 2 * (4 * a * c + b * c) ≤ Real.sqrt 17 * (a ^ 2 + b ^ 2 + c ^ 2) := by
        have h4 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num)
        nlinarith [sq_nonneg (a - 4 * b), sq_nonneg (c - Real.sqrt 17 * b), sq_nonneg (c - (4 * a + b) * (Real.sqrt 17) / 17), sq_nonneg (4 * a + b - Real.sqrt 17 * c), sq_nonneg (a - 4 * b), Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      linarith
    have h2 : x = (4 * a * c + b * c) / (a ^ 2 + b ^ 2 + c ^ 2) := by
      linarith [h_eq]
    linarith [h1, h2]