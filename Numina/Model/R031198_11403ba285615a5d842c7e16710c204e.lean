import Mathlib


theorem algebra_221446 {A B C : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (h : 1 / A + 1 / B + 1 / C = 1 / (A + B + C)) (n : ℕ) (hn : Odd n) :
    1 / A ^ n + 1 / B ^ n + 1 / C ^ n = 1 / (A ^ n + B ^ n + C ^ n) := by

  have h1 : A + B + C ≠ 0 := by
    by_contra h2
    have h3 : 1 / (A + B + C) = 0 := by
      rw [show A + B + C = (0 : ℝ) by linarith]
      norm_num
    have h4 : 1 / A + 1 / B + 1 / C = 0 := by linarith [h, h3]
    field_simp [hA, hB, hC] at h4
    <;> nlinarith [sq_pos_of_ne_zero hA, sq_pos_of_ne_zero hB, sq_pos_of_ne_zero hC]

  have h2 : (A + B) * (B + C) * (C + A) = 0 := by
    field_simp [hA, hB, hC, h1] at h ⊢
    nlinarith [sq_pos_of_ne_zero hA, sq_pos_of_ne_zero hB, sq_pos_of_ne_zero hC, sq_nonneg (A * B), sq_nonneg (B * C), sq_nonneg (C * A)]

  cases' (mul_eq_zero.mp h2) with h3 h4
  · cases' (mul_eq_zero.mp h3) with h5 h6
    · -- Case where $A + B = 0$, so $A = -B$.
      have h7 : A + B = 0 := by linarith
      have h8 : A = -B := by linarith
      have h9 : A ^ n = - (B ^ n : ℝ) := by
        rw [show A = -B by linarith]
        have h10 : (-B : ℝ) ^ n = - (B ^ n : ℝ) := by
          have h11 : Odd n := hn
          have h12 : (-B : ℝ) ^ n = - (B ^ n : ℝ) := by
            apply Odd.neg_pow
            exact h11
          linarith
        linarith
      have h10 : A ^ n + B ^ n + C ^ n = C ^ n := by
        have h11 : A ^ n + B ^ n = 0 := by
          linarith [h9]
        linarith
      have h12 : 1 / A ^ n + 1 / B ^ n = 0 := by
        have h13 : 1 / A ^ n = - (1 / B ^ n : ℝ) := by
          have h14 : A ^ n = - (B ^ n : ℝ) := h9
          have h15 : 1 / A ^ n = 1 / (- (B ^ n : ℝ)) := by
            rw [show A ^ n = - (B ^ n : ℝ) by linarith]
          rw [h15]
          have h16 : 1 / (- (B ^ n : ℝ)) = - (1 / (B ^ n : ℝ) : ℝ) := by
            ring
          linarith
        linarith
      have h17 : 1 / A ^ n + 1 / B ^ n + 1 / C ^ n = 1 / C ^ n := by
        have h18 : 1 / A ^ n + 1 / B ^ n = 0 := h12
        linarith
      rw [h17, h10]
    · -- Case where $B + C = 0$, so $B = -C$.
      have h7 : B + C = 0 := by linarith
      have h8 : B = -C := by linarith
      have h9 : B ^ n = - (C ^ n : ℝ) := by
        rw [show B = -C by linarith]
        have h10 : (-C : ℝ) ^ n = - (C ^ n : ℝ) := by
          have h11 : Odd n := hn
          have h12 : (-C : ℝ) ^ n = - (C ^ n : ℝ) := by
            apply Odd.neg_pow
            exact h11
          linarith
        linarith
      have h10 : A ^ n + B ^ n + C ^ n = A ^ n := by
        have h11 : B ^ n + C ^ n = 0 := by
          linarith [h9]
        linarith
      have h12 : 1 / B ^ n + 1 / C ^ n = 0 := by
        have h13 : 1 / B ^ n = - (1 / C ^ n : ℝ) := by
          have h14 : B ^ n = - (C ^ n : ℝ) := h9
          have h15 : 1 / B ^ n = 1 / (- (C ^ n : ℝ)) := by
            rw [show B ^ n = - (C ^ n : ℝ) by linarith]
          rw [h15]
          have h16 : 1 / (- (C ^ n : ℝ)) = - (1 / (C ^ n : ℝ) : ℝ) := by
            ring
          linarith
        linarith
      have h17 : 1 / A ^ n + 1 / B ^ n + 1 / C ^ n = 1 / A ^ n := by
        have h18 : 1 / B ^ n + 1 / C ^ n = 0 := h12
        linarith
      rw [h17, h10]
  · -- Case where $C + A = 0$, so $C = -A$.
    have h7 : C + A = 0 := by linarith
    have h8 : C = -A := by linarith
    have h9 : C ^ n = - (A ^ n : ℝ) := by
      rw [show C = -A by linarith]
      have h10 : (-A : ℝ) ^ n = - (A ^ n : ℝ) := by
        have h11 : Odd n := hn
        have h12 : (-A : ℝ) ^ n = - (A ^ n : ℝ) := by
          apply Odd.neg_pow
          exact h11
        linarith
      linarith
    have h10 : A ^ n + B ^ n + C ^ n = B ^ n := by
      have h11 : A ^ n + C ^ n = 0 := by
        linarith [h9]
      linarith
    have h12 : 1 / A ^ n + 1 / C ^ n = 0 := by
      have h13 : 1 / A ^ n = - (1 / C ^ n : ℝ) := by
        have h14 : C ^ n = - (A ^ n : ℝ) := h9
        have h15 : 1 / C ^ n = 1 / (- (A ^ n : ℝ)) := by
          rw [show C ^ n = - (A ^ n : ℝ) by linarith]
        have h16 : 1 / (- (A ^ n : ℝ)) = - (1 / (A ^ n : ℝ) : ℝ) := by
          ring
        have h17 : (1 / C ^ n : ℝ) = - (1 / (A ^ n : ℝ) : ℝ) := by
          rw [h15, h16]
        linarith
      linarith
    have h17 : 1 / A ^ n + 1 / B ^ n + 1 / C ^ n = 1 / B ^ n := by
      have h18 : 1 / A ^ n + 1 / C ^ n = 0 := h12
      linarith
    rw [h17, h10]