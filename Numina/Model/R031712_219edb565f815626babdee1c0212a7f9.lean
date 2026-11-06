import Mathlib

open Real

theorem inequalities_105967 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + b) * (b + c) * (c + a) = 1) :
    1 / 2 ≤ a ^ 2 / (1 + sqrt (b * c)) + b ^ 2 / (1 + sqrt (c * a)) + c ^ 2 / (1 + sqrt (a * b)) := by

  have h1 : sqrt (b * c) = Real.sqrt b * Real.sqrt c := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h1' : sqrt (c * a) = Real.sqrt c * Real.sqrt a := by
    rw [Real.sqrt_mul]
    all_goals nlinarith
  have h1'' : sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul]
    all_goals nlinarith

  have h2 : ∀ x y : ℝ, 0 < x → 0 < y → Real.sqrt (x * y) ≤ (x + y) / 2 := by
    intro x y hx hy
    have h3 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
      rw [Real.sqrt_mul]
      all_goals nlinarith
    have h4 : Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith), sq_nonneg (x - y)]
    linarith [h3, h4]

  have h3 : a ^ 2 / (1 + sqrt (b * c)) ≥ (2 * a ^ 2) / (2 + b + c) := by
    have h4 : sqrt (b * c) ≤ (b + c) / 2 := h2 b c hb hc
    have h5 : (1 + sqrt (b * c)) ≤ (1 + (b + c) / 2) := by linarith [h4]
    have h6 : 0 < (1 + (b + c) / 2) := by nlinarith
    have h7 : 0 < (1 + sqrt (b * c)) := by
      have h8 : sqrt (b * c) > 0 := by positivity
      linarith [h8]
    have h8 : a ^ 2 / (1 + sqrt (b * c)) ≥ a ^ 2 / (1 + (b + c) / 2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h9 : a ^ 2 / (1 + (b + c) / 2) = (2 * a ^ 2) / (2 + b + c) := by
      field_simp
      <;> ring
    linarith [h8, h9]

  have h4 : b ^ 2 / (1 + sqrt (c * a)) ≥ (2 * b ^ 2) / (2 + c + a) := by
    have h5 : sqrt (c * a) ≤ (c + a) / 2 := h2 c a hc ha
    have h6 : (1 + sqrt (c * a)) ≤ (1 + (c + a) / 2) := by linarith [h5]
    have h7 : 0 < (1 + (c + a) / 2) := by nlinarith
    have h8 : 0 < (1 + sqrt (c * a)) := by
      have h9 : sqrt (c * a) > 0 := by positivity
      linarith [h9]
    have h9 : b ^ 2 / (1 + sqrt (c * a)) ≥ b ^ 2 / (1 + (c + a) / 2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h10 : b ^ 2 / (1 + (c + a) / 2) = (2 * b ^ 2) / (2 + c + a) := by
      field_simp
      <;> ring
    linarith [h9, h10]

  have h5 : c ^ 2 / (1 + sqrt (a * b)) ≥ (2 * c ^ 2) / (2 + a + b) := by
    have h6 : sqrt (a * b) ≤ (a + b) / 2 := h2 a b ha hb
    have h7 : (1 + sqrt (a * b)) ≤ (1 + (a + b) / 2) := by linarith [h6]
    have h8 : 0 < (1 + (a + b) / 2) := by nlinarith
    have h9 : 0 < (1 + sqrt (a * b)) := by
      have h10 : sqrt (a * b) > 0 := by positivity
      linarith [h10]
    have h10 : c ^ 2 / (1 + sqrt (a * b)) ≥ c ^ 2 / (1 + (a + b) / 2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    have h11 : c ^ 2 / (1 + (a + b) / 2) = (2 * c ^ 2) / (2 + a + b) := by
      field_simp
      <;> ring
    linarith [h10, h11]

  have h6 : a ^ 2 / (1 + sqrt (b * c)) + b ^ 2 / (1 + sqrt (c * a)) + c ^ 2 / (1 + sqrt (a * b)) ≥ (2 * a ^ 2) / (2 + b + c) + (2 * b ^ 2) / (2 + c + a) + (2 * c ^ 2) / (2 + a + b) := by
    linarith [h3, h4, h5]

  have h7 : (2 * a ^ 2) / (2 + b + c) + (2 * b ^ 2) / (2 + c + a) + (2 * c ^ 2) / (2 + a + b) ≥ 1 / 2 := by
    have h12 : (a + b) + (b + c) + (c + a) ≥ 3 := by
      nlinarith [sq_nonneg (a + b - (b + c)), sq_nonneg (b + c - (c + a)), sq_nonneg (c + a - (a + b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    have h3 : (2 * a ^ 2) / (2 + b + c) + (2 * b ^ 2) / (2 + c + a) + (2 * c ^ 2) / (2 + a + b) ≥ 1 / 2 := by
      have h10 : (2 * a ^ 2) / (2 + b + c) + (2 * b ^ 2) / (2 + c + a) + (2 * c ^ 2) / (2 + a + b) - 1 / 2 ≥ 0 := by
        have h12 : (a + b) + (b + c) + (c + a) ≥ 3 := by
          nlinarith [sq_nonneg (a + b - (b + c)), sq_nonneg (b + c - (c + a)), sq_nonneg (c + a - (a + b)), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have h13 : (2 * a ^ 2) / (2 + b + c) + (2 * b ^ 2) / (2 + c + a) + (2 * c ^ 2) / (2 + a + b) - 1 / 2 = 
          (4 * a ^ 2 * (2 + c + a) * (2 + a + b) + 4 * b ^ 2 * (2 + b + c) * (2 + a + b) + 4 * c ^ 2 * (2 + b + c) * (2 + c + a) - (2 + b + c) * (2 + c + a) * (2 + a + b)) / (2 * (2 + b + c) * (2 + c + a) * (2 + a + b)) := by
          field_simp
          ring
        rw [h13]
        have h14 : 0 ≤ 4 * a ^ 2 * (2 + c + a) * (2 + a + b) + 4 * b ^ 2 * (2 + b + c) * (2 + a + b) + 4 * c ^ 2 * (2 + b + c) * (2 + c + a) - (2 + b + c) * (2 + c + a) * (2 + a + b) := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, h12, mul_pos ha (show 0 < a * b by nlinarith), mul_pos ha (show 0 < a * c by nlinarith), mul_pos hb (show 0 < b * c by nlinarith)]
        have h15 : 0 < 2 * (2 + b + c) * (2 + c + a) * (2 + a + b) := by positivity
        apply div_nonneg
        linarith
        all_goals positivity
      linarith
    linarith

  linarith [h6, h7]