import Mathlib

theorem algebra_207748 (a d : ℝ) (h₀ : a > a - d) (h₁ : a - d > a - 2 * d)
    (h₂ : a - 2 * d > a - 3 * d) (h₃ : a - 3 * d > a - 4 * d) (h₄ : a ^ 3 + (a - d) ^ 3 + (a - 2 * d) ^ 3 + (a - 3 * d) ^ 3 + (a - 4 * d) ^ 3 = 0)
    (h₅ : a ^ 4 + (a - d) ^ 4 + (a - 2 * d) ^ 4 + (a - 3 * d) ^ 4 + (a - 4 * d) ^ 4 = 136) :
    a - 4 * d = -2 * Real.sqrt 2 := by
  have h6 : 5 * a ^ 3 - 30 * a ^ 2 * d + 90 * a * d ^ 2 - 100 * d ^ 3 = 0 := by
    ring_nf at h₄ ⊢
    linarith
  have h7 : (a - 2 * d) * (a ^ 2 - 4 * a * d + 10 * d ^ 2) = 0 := by
    nlinarith [h6]

  cases' (mul_eq_zero.mp h7) with h8 h9
  · -- Assume h8 : a - 2 * d = 0 
    have ha : a = 2 * d := by linarith
    rw [ha] at h₅
    have h8 : 34 * d ^ 4 = 136 := by
      ring_nf at h₅ ⊢
      linarith
    have h9 : d ^ 4 = 4 := by
      nlinarith
    have h10 : (d ^ 2) ^ 2 = 4 := by
      nlinarith
    have h11 : d ^ 2 = 2 := by
      have h12 : d ^ 2 ≥ 0 := sq_nonneg d
      have h13 : (d ^ 2) = 2 ∨ (d ^ 2) = -2 := by
        have h14 : (d ^ 2) ^ 2 - 4 = 0 := by linarith
        have h15 : (d ^ 2 - 2) * (d ^ 2 + 2) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h15) with h16 h17
        · -- Assume h16
          left
          linarith
        · -- Assume h17
          right
          nlinarith
      cases h13 with
      | inl h18 => linarith
      | inr h18 => 
        nlinarith [sq_nonneg d]
    have h13 : d > 0 := by
      nlinarith
    have h14 : d = Real.sqrt 2 := by
      have h15 : d ^ 2 = 2 := h11
      have h16 : d > 0 := h13
      have h17 : d = Real.sqrt 2 := by
        rw [← h15]
        field_simp
      linarith
    have ha' : a = 2 * Real.sqrt 2 := by
      rw [show d = Real.sqrt 2 by linarith [h14]] at ha
      linarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), sq_pos_of_pos (show d > 0 by linarith)]
  · -- Assume h9 : a ^ 2 - 4 * a * d + 10 * d ^ 2 = 0
    have ha1 : a ^ 2 - 4 * a * d + 10 * d ^ 2 = 0 := by
      linarith
    have h8 : d > 0 := by
      nlinarith
    have h10 : (a - 2 * d) ^ 2 + 6 * d ^ 2 = 0 := by
      nlinarith
    have h11 : (a - 2 * d) ^ 2 ≥ 0 := by nlinarith [sq_nonneg (a - 2 * d)]
    have h12 : 6 * d ^ 2 ≥ 0 := by nlinarith [sq_nonneg d]
    have h13 : (a - 2 * d) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 2 * d), sq_nonneg d]
    have h14 : 6 * d ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 2 * d), sq_nonneg d]
    have h15 : d ^ 2 = 0 := by
      nlinarith
    have h16 : d = 0 := by
      nlinarith
    linarith