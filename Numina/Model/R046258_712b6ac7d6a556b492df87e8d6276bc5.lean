import Mathlib

open Real

theorem inequalities_225925 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a^2 + b^2 + c^2 = 1 ∧ x = a * b / c + b * c / a + c * a / b} (Real.sqrt 3) := by
  constructor
  · -- Show that Real.sqrt 3 is in the set
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show a > 0
      positivity
    constructor
    · -- Show b > 0
      positivity
    constructor
    · -- Show c > 0
      positivity
    constructor
    · -- Show a^2 + b^2 + c^2 = 1
      have h1 : (Real.sqrt 3 / 3 : ℝ) ^ 2 = (3 : ℝ) / 9 := by
        calc
          (Real.sqrt 3 / 3 : ℝ) ^ 2 = (Real.sqrt 3) ^ 2 / 9 := by ring_nf
          _ = (3 : ℝ) / 9 := by
            rw [Real.sq_sqrt]
            all_goals norm_num
      nlinarith [h1]
    · -- Show that Real.sqrt 3 = a * b / c + b * c / a + c * a / b
      field_simp
      <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Show that Real.sqrt 3 is the least
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h, hx⟩
    -- Show that sqrt 3 ≤ S
    have h1 : a * b / c + b * c / a + c * a / b ≥ Real.sqrt 3 := by
      have h2 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ 3 := by
        have h3 : a * b / c + b * c / a + c * a / b ≥ 0 := by positivity
        have h4 : (a * b / c + b * c / a + c * a / b) ^ 2 = (a * b / c) ^ 2 + (b * c / a) ^ 2 + (c * a / b) ^ 2 + 2 * ((a * b / c) * (b * c / a) + (a * b / c) * (c * a / b) + (b * c / a) * (c * a / b)) := by ring
        rw [h4]
        have h5 : (a * b / c) * (b * c / a) = b ^ 2 := by
          field_simp
          <;> ring
        have h6 : (a * b / c) * (c * a / b) = a ^ 2 := by
          field_simp
          <;> ring
        have h7 : (b * c / a) * (c * a / b) = c ^ 2 := by
          field_simp
          <;> ring
        rw [h5, h6, h7]
        nlinarith [sq_nonneg (a * b / c - b * c / a), sq_nonneg (a * b / c - c * a / b), sq_nonneg (b * c / a - c * a / b), 
                  h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
                ]
      have h3_pos : Real.sqrt 3 ≥ 0 := by positivity
      have h4 : (a * b / c + b * c / a + c * a / b) ≥ 0 := by positivity
      have h5 : (a * b / c + b * c / a + c * a / b) ^ 2 ≥ (Real.sqrt 3) ^ 2 := by
        nlinarith [h2, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_nonneg 3]
      nlinarith [Real.sqrt_nonneg 3, h4]
    linarith [h1, hx]