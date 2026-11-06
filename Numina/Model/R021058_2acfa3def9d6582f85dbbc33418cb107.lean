import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_98974 :
  {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ |
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    2 * a + 3 * b + 5 * c + 7 * d ≤ 174 - 8 / a - 27 / b - 125 / c - 343 / d} =
  {(2, 3, 5, 7)} := by 
  ext ⟨a, b, c, d⟩
  simp [-one_div]
  constructor
  · -- Forward implication
    intro h
    rcases h with ⟨ha, hb, hc, hd, h⟩
    have h1 : 2 * a + 3 * b + 5 * c + 7 * d + 8 / a + 27 / b + 125 / c + 343 / d ≤ 174 := by
      have h2 : 2 * a + 3 * b + 5 * c + 7 * d ≤ 174 - 8 / a - 27 / b - 125 / c - 343 / d := by
        linarith [h]
      have h3 : 2 * a + 3 * b + 5 * c + 7 * d + 8 / a + 27 / b + 125 / c + 343 / d ≤ 174 := by 
        have h4 : 2 * a + 3 * b + 5 * c + 7 * d ≤ 174 - 8 / a - 27 / b - 125 / c - 343 / d := h2 
        have h5 : (2 * a + 3 * b + 5 * c + 7 * d) + (8 / a + 27 / b + 125 / c + 343 / d) ≤ 174 := by 
          nlinarith [h4]
        linarith [h5]
      linarith 
    have h2 : 2 * a + 8 / a ≥ 8 := by 
      have h3 : a > 0 := by linarith 
      have h4 : 2 * a + 8 / a - (8 : ℝ) ≥ 0 := by
        have h5 : 2 * a + 8 / a - (8 : ℝ) = (2 * (a - 2) ^ 2) / a := by 
          field_simp 
          ring 
        rw [h5]
        have h6 : a > 0 := by linarith 
        have h7 : (2 * (a - 2) ^ 2) / a ≥ 0 := by 
          apply div_nonneg 
          · -- Show 2 * (a - 2) ^ 2 ≥ 0 
            nlinarith 
          · -- Show a ≥ 0 
            linarith 
        linarith 
      linarith 
    have h3 : 3 * b + 27 / b ≥ 18 := by 
      have h4 : b > 0 := by linarith 
      have h5 : 3 * b + 27 / b - (18 : ℝ) ≥ 0 := by 
        have h6 : 3 * b + 27 / b - (18 : ℝ) = (3 * (b - 3) ^ 2) / b := by 
          field_simp 
          ring 
        rw [h6]
        have h7 : b > 0 := by linarith 
        have h8 : (3 * (b - 3) ^ 2) / b ≥ 0 := by 
          apply div_nonneg 
          · -- Show 3 * (b - 3) ^ 2 ≥ 0 
            nlinarith 
          · -- Show b ≥ 0 
            linarith 
        linarith 
      linarith 
    have h4 : 5 * c + 125 / c ≥ 50 := by 
      have h5 : c > 0 := by linarith 
      have h6 : 5 * c + 125 / c - (50 : ℝ) ≥ 0 := by 
        have h7 : 5 * c + 125 / c - (50 : ℝ) = (5 * (c - 5) ^ 2) / c := by 
          field_simp 
          ring 
        rw [h7]
        have h8 : c > 0 := by linarith 
        have h9 : (5 * (c - 5) ^ 2) / c ≥ 0 := by 
          apply div_nonneg 
          · -- Show 5 * (c - 5) ^ 2 ≥ 0 
            nlinarith 
          · -- Show c ≥ 0 
            linarith 
        linarith 
      linarith 
    -- Prove the fourth inequality: 7 * d + 343 / d >= 98
    have h5 : 7 * d + 343 / d ≥ 98 := by 
      have h6 : d > 0 := by linarith 
      have h7 : 7 * d + 343 / d - (98 : ℝ) ≥ 0 := by 
        have h8 : 7 * d + 343 / d - (98 : ℝ) = (7 * (d - 7) ^ 2) / d := by 
          field_simp 
          ring 
        rw [h8]
        have h9 : d > 0 := by linarith 
        have h10 : (7 * (d - 7) ^ 2) / d ≥ 0 := by 
          apply div_nonneg 
          · -- Show 7 * (d - 7) ^ 2 ≥ 0 
            nlinarith 
          · -- Show d ≥ 0 
            linarith 
        linarith 
      linarith 
    -- From these equalities infer values a,b,c,d
    have h6 : 2 * a + 8 / a = 8 := by
      nlinarith [h1, h2, h3, h4, h5]
    have h7 : 3 * b + 27 / b = 18 := by
      nlinarith [h1, h2, h3, h4, h5]
    have h8 : 5 * c + 125 / c = 50 := by
      nlinarith [h1, h2, h3, h4, h5]
    have h9 : 7 * d + 343 / d = 98 := by
      nlinarith [h1, h2, h3, h4, h5]
    have ha2 : a = 2 := by
      field_simp at h6
      nlinarith [sq_nonneg (a - 2)]
    have hb2 : b = 3 := by
      field_simp at h7
      nlinarith [sq_nonneg (b - 3)]
    have hc2 : c = 5 := by 
      field_simp at h8
      nlinarith [sq_nonneg (c - 5)]
    have hd2 : d = 7 := by 
      field_simp at h9
      nlinarith [sq_nonneg (d - 7)]
    simp [ha2, hb2, hc2, hd2]
  · -- Backward implication
    rintro ⟨rfl, rfl, rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Check the inequality
      norm_num