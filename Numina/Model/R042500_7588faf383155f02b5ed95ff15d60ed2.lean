import Mathlib

open Real

theorem inequalities_288745 : (∀ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a = c + 1 / d ∧ b = d + 1 / c → a * b ≥ 4 ∧ a * b + c * d ≥ 2 * (1 + sqrt 2)) ∧ (∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a = c + 1 / d ∧ b = d + 1 / c ∧ a * b + c * d = 2 * (1 + sqrt 2)) := by
  constructor
  · -- Prove the main inequalities
    intro a b c d h
    rcases h with ⟨ha, hb, hc, hd, ha_eq, hb_eq⟩
    have h0 : a * b = (c + 1 / d) * (d + 1 / c) := by
      rw [show a = c + 1 / d by linarith [ha_eq], show b = d + 1 / c by linarith [hb_eq]]
    have h1 : a * b = c * d + 1 / (c * d) + 2 := by 
      rw [h0]
      have h2 : c ≠ 0 := by linarith 
      have h3 : d ≠ 0 := by linarith
      field_simp
      <;> ring_nf <;> field_simp
      <;> ring
    have h4 : a * b ≥ 4 := by
      rw [h1]
      have h5 : c * d + 1 / (c * d) ≥ 2 := by
        have h6 : c * d + 1 / (c * d) - 2 ≥ 0 := by
          have h7 : (c * d + 1 / (c * d) - 2) = ( (c * d) ^ 2 - 2 * (c * d) + 1 ) / (c * d) := by
            field_simp
            ring
          rw [h7]
          have h8 : (c * d) ≠ 0 := by
            nlinarith [hc, hd]
          have h9 : 0 < c * d := by
            nlinarith [hc, hd]
          have h10 : ( (c * d) ^ 2 - 2 * (c * d) + 1 ) ≥ 0 := by
            nlinarith [sq_nonneg (c * d - 1)]
          apply div_nonneg
          exact h10
          nlinarith
        linarith
      nlinarith [Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 2]
    -- Second part: prove that a * b + c * d >= 2 * sqrt(2) + 2
    have h9 : a * b + c * d = 2 * (c * d) + 1 / (c * d) + 2 := by 
      have h10 : a * b = c * d + 2 + 1 / (c * d) := by
        nlinarith [h1]
      have h11 : a * b + c * d = 2 * (c * d) + 2 + 1 / (c * d) := by 
        nlinarith [h10]
      linarith
    have h12 : a * b + c * d ≥ 2 * (1 + sqrt 2) := by 
      have h13 : a * b + c * d = 2 * (c * d) + 1 / (c * d) + 2 := h9
      have h14 : 2 * (c * d) + 1 / (c * d) + 2 ≥ 2 * (1 + sqrt 2) := by
        have hcd_pos : 0 < c * d := by
          nlinarith [hc, hd]
        have h18 : 2 * (c * d) + 1 / (c * d) ≥ 2 * Real.sqrt 2 := by
          have h15 : (2 * (c * d) + 1 / (c * d)) - 2 * Real.sqrt 2 ≥ 0 := by
            have h16 : ( (2 * (c * d) + 1 / (c * d)) - 2 * Real.sqrt 2 ) = ( (2 * (c * d) ^ 2 + 1 - 2 * Real.sqrt 2 * (c * d)) / ((c * d)) ) := by 
              field_simp
              ring_nf
              <;> field_simp
              <;> ring
            rw [h16]
            have h17 : c * d > 0 := by
              nlinarith [hc, hd]
            have h18 : (2 * (c * d) ^ 2 + 1 - 2 * Real.sqrt 2 * (c * d)) ≥ 0 := by
              nlinarith [sq_nonneg (2 * (c * d) ^ 2 - 1), sq_nonneg ((c * d) * (c * d) * Real.sqrt 2 - Real.sqrt 2), sq_nonneg ((c * d) * (c * d) * (Real.sqrt 2) ^ 2 - (Real.sqrt 2) ^ 2), sq_nonneg ((c * d) - Real.sqrt 2 / 2), sq_nonneg (Real.sqrt 2 - 1 / Real.sqrt 2), Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, sq_nonneg (2 * (c * d) ^ 2 - 1), sq_nonneg ((c * d) - Real.sqrt 2 / 2), sq_nonneg (c * d * (2 / c * d) - Real.sqrt 2), Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            apply div_nonneg 
            exact h18 
            positivity
          linarith 
        nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), h18]
      linarith [h13, h14, Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor 
    · exact h4 
    · exact h12 
  · -- Show existence 
    use 1 + Real.sqrt 2, 1 + Real.sqrt 2 / 2, 1, Real.sqrt 2 / 2
    constructor
    · -- Show $a > 0$ 
      nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show $b > 0$ 
      nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show $c > 0$ 
      norm_num 
    constructor
    · -- Show $d > 0$ 
      have h01 : Real.sqrt 2 / 2 > 0 := by
        have h02 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)
        nlinarith 
      nlinarith [Real.sqrt_nonneg 2, h01]
    constructor
    · -- Show $a = c + 1/d$ 
      field_simp [Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      <;> ring_nf <;> norm_num [show Real.sqrt 2 * Real.sqrt 2 = 2 by nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)], Real.sqrt_nonneg 2]
    constructor
    · -- Show $b = d + 1/c$ 
      field_simp 
      <;> ring_nf <;> norm_num 
      [show Real.sqrt 2 * Real.sqrt 2 = 2 by nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)], Real.sqrt_nonneg 2]
    · -- Show $a * b + c * d = 2 * (1 + sqrt 2)$ 
      nlinarith [Real.sqrt_nonneg 2, Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 * Real.sqrt 2 * Real.sqrt 2 * (Real.sqrt 2 / (Real.sqrt 2 * Real.sqrt 2)) - (Real.sqrt 2 : ℝ)), sq_nonneg ((Real.sqrt 2 - 2 * Real.sqrt 2 / 2) * (Real.sqrt 2 - 2 * Real.sqrt 2 / 2)), sq_nonneg (Real.sqrt 2 - Real.sqrt 2), sq_nonneg (Real.sqrt 2 - Real.sqrt 2 / 2 - 1)]