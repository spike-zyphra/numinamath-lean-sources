import Mathlib

theorem algebra_13896 (a b c : ℝ) (h₀ : a + b + c = 2) (h₁ : a * b + a * c + b * c = -7)
    (h₂ : a * b * c = -14) :
    max (max a b) c = Real.sqrt 7 := by
  have h3 : (a - 2) * (b - 2) * (c - 2) = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · cases' (mul_eq_zero.mp h4) with h6 h7
    · -- Case a = 2
      have ha : a = 2 := by linarith
      have h8 : b + c = 0 := by linarith [h₀, ha]
      have h9 : b ^ 2 = 7 := by
        have eq1 : a * b + a * c + b * c = -7 := h₁
        rw [ha] at eq1
        have h10 : c = -b := by linarith
        rw [h10] at eq1
        nlinarith
      have hb1 : b = Real.sqrt 7 ∨ b = -Real.sqrt 7 := by
        have h10 : b ^ 2 = 7 := h9
        have h11 : b ^ 2 - 7 = 0 := by linarith
        have h12 : (b - Real.sqrt 7) * (b + Real.sqrt 7) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
        cases (mul_eq_zero.mp h12) with
        | inl h13 =>
          left
          linarith
        | inr h14 =>
          right
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
      cases hb1 with
      | inl hb2 =>
        have hc1 : c = -Real.sqrt 7 := by
          have h10 : b + c = 0 := h8
          linarith
        have h11 : max (max a b) c = Real.sqrt 7 := by
          rw [ha, hb2, hc1]
          have h13 : Real.sqrt 7 > (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          have h14 : max (max (2 : ℝ) (Real.sqrt 7 : ℝ)) (-Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
            have h15 : max (2 : ℝ) (Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
              apply max_eq_right
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
            rw [h15]
            apply max_eq_left
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          linarith
        linarith
      | inr hb2 =>
        have hc1 : c = Real.sqrt 7 := by
          have h10 : b + c = 0 := h8
          linarith
        have h11 : max (max a b) c = Real.sqrt 7 := by
          rw [ha, hb2, hc1]
          have h13 : Real.sqrt 7 > (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          have h14 : max (max (2 : ℝ) (-Real.sqrt 7 : ℝ)) (Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
            have h15 : max (2 : ℝ) (-Real.sqrt 7 : ℝ) = (2 : ℝ) := by
              apply max_eq_left
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
            rw [h15]
            have h16 : max (2 : ℝ) (Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
              apply max_eq_right
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
            linarith
          linarith
        linarith
    · -- Case b = 2
      have hb : b = 2 := by linarith
      have h8 : a + c = 0 := by linarith [h₀, hb]
      have h9 : a ^ 2 = 7 := by
        have eq1 : a * b + a * c + b * c = -7 := h₁
        rw [hb] at eq1
        have h10 : c = -a := by linarith
        rw [h10] at eq1
        nlinarith
      have ha1 : a = Real.sqrt 7 ∨ a = -Real.sqrt 7 := by
        have h10 : a ^ 2 = 7 := h9
        have h11 : a ^ 2 - 7 = 0 := by linarith
        have h12 : (a - Real.sqrt 7) * (a + Real.sqrt 7) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
        cases (mul_eq_zero.mp h12) with
        | inl h13 =>
          left
          linarith
        | inr h14 =>
          right
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
      cases ha1 with
      | inl ha2 =>
        have hc1 : c = -Real.sqrt 7 := by
          have h10 : a + c = 0 := h8
          linarith
        have h11 : max (max a b) c = Real.sqrt 7 := by
          rw [ha2, hb, hc1]
          have h13 : Real.sqrt 7 > (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          have h14 : max (max (Real.sqrt 7 : ℝ) (2 : ℝ)) (-Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
            have h15 : max (Real.sqrt 7 : ℝ) (2 : ℝ) = Real.sqrt 7 := by
              apply max_eq_left
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
            rw [h15]
            apply max_eq_left
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          linarith
        linarith
      | inr ha2 =>
        have hc1 : c = Real.sqrt 7 := by
          have h10 : a + c = 0 := h8
          linarith
        have h11 : max (max a b) c = Real.sqrt 7 := by
          rw [ha2, hb, hc1]
          have h13 : Real.sqrt 7 > (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          have h14 : max (max (-Real.sqrt 7 : ℝ) (2 : ℝ)) (Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
            have h15 : max (-Real.sqrt 7 : ℝ) (2 : ℝ) = (2 : ℝ) := by
              apply max_eq_right
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
            rw [h15]
            have h16 : max (2 : ℝ) (Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
              apply max_eq_right
              nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
            linarith
          linarith
        linarith
  · -- Case c = 2
    have hc : c = 2 := by linarith
    have h8 : a + b = 0 := by linarith [h₀, hc]
    have h9 : a ^ 2 = 7 := by
      have eq1 : a * b + a * c + b * c = -7 := h₁
      rw [hc] at eq1
      have h10 : b = -a := by linarith
      rw [h10] at eq1
      nlinarith
    have ha1 : a = Real.sqrt 7 ∨ a = -Real.sqrt 7 := by
      have h10 : a ^ 2 = 7 := h9
      have h11 : a ^ 2 - 7 = 0 := by linarith
      have h12 : (a - Real.sqrt 7) * (a + Real.sqrt 7) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
      cases (mul_eq_zero.mp h12) with
      | inl h13 =>
        left
        linarith
      | inr h14 =>
        right
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num : (0 : ℝ) < 7), Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num : (0 : ℝ) ≤ 7)]
    cases ha1 with
    | inl ha2 =>
      have hb1 : b = -Real.sqrt 7 := by
        have h10 : a + b = 0 := h8
        linarith
      have h11 : max (max a b) c = Real.sqrt 7 := by
        rw [ha2, hb1, hc]
        have h13 : Real.sqrt 7 > (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
        have h14 : max (max (Real.sqrt 7 : ℝ) (-Real.sqrt 7 : ℝ)) (2 : ℝ) = Real.sqrt 7 := by
          have h15 : max (Real.sqrt 7 : ℝ) (-Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
            apply max_eq_left
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          rw [h15]
          apply max_eq_left
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
        linarith
      linarith
    | inr ha2 =>
      have hb1 : b = Real.sqrt 7 := by
        have h10 : a + b = 0 := h8
        linarith
      have h11 : max (max a b) c = Real.sqrt 7 := by
        rw [ha2, hb1, hc]
        have h13 : Real.sqrt 7 > (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
        have h14 : max (max (-Real.sqrt 7 : ℝ) (Real.sqrt 7 : ℝ)) (2 : ℝ) = Real.sqrt 7 := by
          have h15 : max (-Real.sqrt 7 : ℝ) (Real.sqrt 7 : ℝ) = Real.sqrt 7 := by
            apply max_eq_right
            nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
          rw [h15]
          apply max_eq_left
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num)]
        linarith
      linarith