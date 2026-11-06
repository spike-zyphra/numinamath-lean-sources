import Mathlib

theorem algebra_120847 {a b c : ℝ} (hmul : a * b * c = 1) (hsum : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  have ane0 : a ≠ 0 := by
    by_contra h
    rw [h] at hmul
    nlinarith
  have bne0 : b ≠ 0 := by
    by_contra h
    rw [h] at hmul
    nlinarith
  have cne0 : c ≠ 0 := by
    by_contra h
    rw [h] at hmul
    nlinarith
  have h1 : 1 / a = b * c := by
    have h22 : a * b * c = 1 := hmul
    field_simp [ane0]
    <;> nlinarith

  have h11 : 1 / b = a * c := by
    have h33 : a * b * c = 1 := hmul
    field_simp [bne0]
    <;> nlinarith
  
  have h22 : 1 / c = a * b := by
    have h44 : a * b * c = 1 := hmul
    field_simp [cne0]
    <;> nlinarith

  rw [h1, h11, h22] at hsum

  -- Now the inequality hsum is expressed in terms of a, b, c

  by_cases ha : a > 1
  · -- Assume h: a > 1
    by_cases hb : b > 1
    · -- Assume hb: b > 1
      -- From hmul: a * b * c = 1, so c = 1/(a * b)
      -- Since a > 1 and b > 1, so a * b > 1, so 1/(a * b) < 1
      have h5 : c < 1 := by
        nlinarith [hmul, mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), sq_nonneg (a * b - 1)]

      -- Now contradiction about hsum: a + b + c > b * c + a * c + a * b
      -- Substitute c < 1, but nlinarith is required here
      -- However, this will fail because it is not valid as shown earlier
      exfalso
      -- Substitute c = 1/(a * b)
      -- Since a > 1 and b > 1, we have c < 1
      -- Let's establish the contradiction: a + b + c ≤ b * c + a * c + a * b
      -- Since a > 1, b > 1, we have c > 0
      have h7 : a + b + c ≤ b * c + a * c + a * b := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), hmul, sq_nonneg (a - 1), sq_nonneg (c - 1), sq_nonneg (b - c), sq_nonneg ((b - 1) * (c - 1)), mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < b - 1 by linarith)]
      linarith
    · -- Assume hb: ¬(b > 1)
      by_cases hc : c > 1
      · -- Assume hc: c > 1
        -- Contradiction still possible
        exfalso
        -- Substitute and show inconsistency
        have h7 : a + b + c ≤ b * c + a * c + a * b := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), hmul, sq_nonneg (a - 1), sq_nonneg (c - 1), sq_nonneg (b - c), sq_nonneg ((b - 1) * (c - 1)), mul_pos (show (0 : ℝ) < a - 1 by linarith) (show (0 : ℝ) < c - 1 by linarith)]
        linarith
      · -- Assume hc: ¬(c > 1)
        have h4 : b ≤ 1 := by linarith
        have h5 : c ≤ 1 := by linarith
        left
        -- Now need to prove: a > 1 ∧ b ≤ 1 ∧ c ≤ 1
        exact ⟨ha, h4, h5⟩
  · -- Assume ha: ¬(a > 1)
    -- So we have a ≤ 1
    by_cases hb : b > 1
    · -- Assume hb: b > 1
      by_cases hc : c > 1
      · -- Assume hc: c > 1
        -- Let's establish contradiction
        exfalso
        -- Substitute and show inconsistency
        have h7 : a + b + c ≤ b * c + a * c + a * b := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc), hmul, sq_nonneg (a - 1), sq_nonneg (c - 1), sq_nonneg (b - c), sq_nonneg ((b - 1) * (c - 1)), mul_pos (show (0 : ℝ) < b - 1 by linarith) (show (0 : ℝ) < c - 1 by linarith)]
        linarith
      · -- Assume hc: ¬(c > 1)
        have h4 : a ≤ 1 := by linarith
        have h5 : c ≤ 1 := by linarith
        right
        left
        exact ⟨hb, h4, h5⟩
    · -- Assume hb: ¬(b > 1)
      by_cases hc : c > 1
      · -- Assume hc: c > 1
        -- Need to derive all constraints here
        have h4 : a ≤ 1 := by linarith
        have h5 : b ≤ 1 := by linarith
        right
        right
        exact ⟨hc, h4, h5⟩
      · -- Assume hc: ¬(c > 1)
        -- This contradiction is important
        exfalso
        -- Substitute and show inconsistency
        have h11 : a ≤ 1 := by linarith
        have h44 : b ≤ 1 := by linarith
        have h55 : c ≤ 1 := by linarith
        have h6 : a + b + c ≤ b * c + a * c + a * b := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_nonneg (show (0 : ℝ) ≤ 1 - a by nlinarith) (show (0 : ℝ) ≤ 1 - b by nlinarith), mul_nonneg (show (0 : ℝ) ≤ 1 - a by nlinarith) (show (0 : ℝ) ≤ 1 - c by nlinarith), mul_nonneg (show (0 : ℝ) ≤ 1 - b by nlinarith) (show (0 : ℝ) ≤ 1 - c by nlinarith), sq_nonneg (a * b * c - 1)]
        linarith