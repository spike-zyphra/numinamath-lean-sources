import Mathlib

theorem algebra_2961 {t : ℝ} : ∃ n : ℕ, 0 ≤ 7 - t ∧ 0 ≤ 7 + t ∧ n = Real.sqrt (7 - t) + Real.sqrt (7 + t) ↔
    t = 4 * Real.sqrt 3 ∨ t = -4 * Real.sqrt 3 := by 
  use 4
  constructor
  · -- Forward: from n=4 derive t = ±4√3
    rintro ⟨h₁, h₂, hn⟩
    have h3 : Real.sqrt (7 - t) + Real.sqrt (7 + t) = (4 : ℝ) := by
      norm_num at hn ⊢
      linarith [hn]
    have h7 : (Real.sqrt (7 - t) : ℝ) ^ 2 = 7 - t := by
      rw [Real.sq_sqrt]
      linarith [h₁]
    have h8 : (Real.sqrt (7 + t) : ℝ) ^ 2 = 7 + t := by
      rw [Real.sq_sqrt]
      linarith [h₂]
    have h14 : (t) ^ 2 = 48 := by
      have h6 : Real.sqrt (7 - t) + Real.sqrt (7 + t) = (4 : ℝ) := h3
      have h13 : Real.sqrt (7 - t) * Real.sqrt (7 + t) = 1 := by
        have h9 : (Real.sqrt (7 - t) + Real.sqrt (7 + t) ) ^ 2 = 16 := by
          rw [h3]
          norm_num
        nlinarith [h7, h8, h9, Real.sqrt_nonneg (7 - t), Real.sqrt_nonneg (7 + t)]
      nlinarith [Real.sqrt_nonneg (7 - t), Real.sqrt_nonneg (7 + t), h7, h8, h13]
    have h17 : (t - 4 * Real.sqrt 3) * (t + 4 * Real.sqrt 3) = 0 := by
      have h12 : (4 * Real.sqrt 3) ^2 = 48 := by
        calc
          (4 * Real.sqrt 3) ^2 = 16 * (Real.sqrt 3) ^2 := by ring
          _ = 16 * (3 : ℝ) := by
            rw [Real.sq_sqrt]
            all_goals norm_num
          _ = 48 := by norm_num
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h17) with h16 h15
    · -- Case where t -4√3 =0
      left
      linarith
    · -- Case where t +4√3 =0
      right
      nlinarith
  · -- Backward: from t = ±4√3 derive n=4
    rintro (h | h)
    · -- Case where t =4 * Real.sqrt 3
      have ht : t = 4 * Real.sqrt 3 := by
        linarith
      constructor
      · -- Show 0 ≤ 7 - t
        rw [ht]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      constructor
      · -- Show 0 ≤ 7 + t
        rw [ht]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      · -- Show 4 = Real.sqrt (7 - t) + Real.sqrt (7 + t)
        have h74 : Real.sqrt (7 - t) + Real.sqrt (7 + t) = (4 : ℝ) := by 
          rw [ht]
          have h7 : Real.sqrt (7 - (4 * Real.sqrt 3)) = 2 - Real.sqrt 3 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          have h8 : Real.sqrt (7 + (4 * Real.sqrt 3)) = 2 + Real.sqrt 3 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          rw [h7, h8]
          <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        norm_num at h74 ⊢
        all_goals linarith [h74]
    · -- Case where t = -4 * Real.sqrt 3
      have ht : t = -4 * Real.sqrt 3 := by
        linarith
      constructor
      · -- Show 0 ≤ 7 - t
        rw [ht]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      constructor
      · -- Show 0 ≤ 7 + t
        rw [ht]
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
      · -- Show 4 = Real.sqrt (7 - t) + Real.sqrt (7 + t)
        have h74 : Real.sqrt (7 - t) + Real.sqrt (7 + t) = (4 : ℝ) := by 
          rw [ht]
          have h7 : Real.sqrt (7 - (-4 * Real.sqrt 3)) = 2 + Real.sqrt 3 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          have h8 : Real.sqrt (7 + (-4 * Real.sqrt 3)) = 2 - Real.sqrt 3 := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
          rw [h7, h8]
          <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
        norm_num at h74 ⊢
        all_goals linarith [h74]