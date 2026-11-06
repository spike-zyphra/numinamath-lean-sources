import Mathlib

theorem algebra_145078 {a b : ℝ} (ha : a ≠ b) (h : a / b + a = b / a + b) :
    1 / a + 1 / b = -1 := by
  have hb : b ≠ 0 := by
    by_contra h1
    have h1 : b = 0 := by linarith
    rw [show b = (0 : ℝ) by linarith [h1]] at h
    have h2 : a = 0 := by
      have h3 : a / (0 : ℝ) = 0 := by
        simp
      rw [h3] at h
      have h4 : (0 : ℝ) / a = 0 := by
        by_cases ha1 : a = 0
        · -- if a = 0, then h gives 0 + 0 = 0 + 0
          rw [ha1]
          norm_num
        ·
          field_simp [ha1]
      nlinarith [h, h4]
    have h3 : a = 0 := by nlinarith [h2]
    have h4 : b = 0 := by
      linarith [h1, h3]
    have h4 : a = b := by
      nlinarith [h3, h4]
    tauto
  have ha1 : a ≠ 0 := by
    by_contra h1
    have h1 : a = 0 := by linarith
    rw [show a = (0 : ℝ) by linarith [h1]] at h
    have h2 : (0 : ℝ) / b = 0 := by
      simp [hb]
    have h3 : b / (0 : ℝ) = 0 := by
      simp
    rw [h2, h3] at h
    have h4 : b = 0 := by
      nlinarith [h]
    have h4 : b = 0 := by
      linarith
    have hb1 : b = 0 := by
      linarith
    tauto
  -- From $a / b + a = b / a + b$, find relationship between $a$ and $b$.
  have h1 : a ^ 2 + a ^ 2 * b = b ^ 2 + a * b ^ 2 := by
    have h2 : a / b + a = b / a + b := h
    have h3 : a ^ 2 + a ^ 2 * b = b ^ 2 + a * b ^ 2 := by
      have h4 : a / b + a = (a ^ 2 + a ^ 2 * b) / (a * b) := by
        field_simp [hb, ha1]
        <;> ring
      have h5 : b / a + b = (b ^ 2 + a * b ^ 2) / (a * b) := by
        field_simp [hb, ha1]
        <;> ring
      rw [h4, h5] at h2
      have h6 : (a ^ 2 + a ^ 2 * b) / (a * b) = (b ^ 2 + a * b ^ 2) / (a * b) := by
        linarith [h2]
      have h7 : (a ^ 2 + a ^ 2 * b) = (b ^ 2 + a * b ^ 2) := by
        have h8 : a * b ≠ 0 := by
          apply mul_ne_zero
          exact ha1
          exact hb
        have h9 : (a ^ 2 + a ^ 2 * b) = (b ^ 2 + a * b ^ 2) := by
          field_simp [h8] at h6 ⊢
          all_goals
            nlinarith [h6]
        linarith [h9]
      linarith [h7]
    exact h3
  -- Rearrange to $a + b + ab = 0$.
  have h3 : (a - b) * (a + b + a * b) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by
      by_contra h10
      have h11 : a = b := by linarith
      tauto
    ), h1]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- case h4 = 0
    have h9 : a = b := by linarith [h4]
    tauto
  · -- from h5 = 0, get $a + b + a * b = 0$
    have h9 : a + b + a * b = 0 := by
      nlinarith [h5]
    -- We need to prove 1/a + 1/b = -1.
    -- First show 1/a + 1/b = (a + b) / (a * b)
    have h22 : 1 / a + 1 / b = (a + b) / (a * b) := by
      field_simp [hb, ha1]
      <;> ring
    rw [h22]
    -- From h9: a+b+ab=0, we get a+b = -ab.
    -- So (a+b)/(ab) = (-ab)/(ab) = -1
    have h23 : a * b ≠ 0 := by
      apply mul_ne_zero
      exact ha1
      exact hb
    have h10 : a + b = - (a * b) := by linarith
    have h11 : (a + b) / (a * b) = -1 := by
      have h24 : a * b ≠ 0 := h23
      rw [show a + b = - (a * b) by linarith]
      field_simp [h24]
    linarith [h11]