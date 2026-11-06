import Mathlib

theorem algebra_10591 {a b c r : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : c ≠ a)
    (h1 : a * (b - c) / (b * (c - a)) = r) (h2 : b * (c - a) / (c * (b - a)) = r)
    (hr : r > 0) :
    r = (Real.sqrt 5 - 1) / 2 := by
  have hb1 : b ≠ 0 := by
    by_contra h
    rw [h] at h1 h2
    field_simp [(show b = 0 by linarith), (show c - a ≠ 0 by
      intro h'
      apply hc
      linarith
    ), (show c ≠ 0 by
      intro h'
      rw [h'] at h2
      field_simp [(show b = 0 by linarith), (show b - a ≠ 0 by
        intro h'
        apply ha
        linarith
      )] at h2
      <;> nlinarith [hr]
    ), (show b - a ≠ 0 by
      intro h'
      apply ha
      linarith
    )] at h1 h2
    all_goals nlinarith [hr]

  have hc1 : c ≠ 0 := by
    by_contra h
    rw [h] at h2
    field_simp [(show c = 0 by linarith), hb1, (show b - a ≠ 0 by
      intro h'
      apply ha
      linarith
    )] at h2
    all_goals nlinarith [hr]

  have eq1 : a * (b - c) = r * (b * (c - a)) := by
    have hne1 : b * (c - a) ≠ 0 := by
      apply mul_ne_zero
      exact hb1
      intro h'
      apply hc
      linarith
    have eq1 : a * (b - c) = r * (b * (c - a)) := by
      have eq1 : a * (b - c) / (b * (c - a)) = r := h1
      field_simp [hne1] at eq1 ⊢
      linarith
    linarith

  have eq2 : b * (c - a) = r * (c * (b - a)) := by
    have hne2 : c * (b - a) ≠ 0 := by
      apply mul_ne_zero
      exact hc1
      intro h'
      apply ha
      linarith
    have eq2 : b * (c - a) = r * (c * (b - a)) := by
      have eq2 : b * (c - a) / (c * (b - a)) = r := h2
      field_simp [hne2] at eq2 ⊢
      linarith
    linarith

  have eq3 : r^2 + r - 1 = 0 := by
    apply (mul_left_inj' (show (b - a) ≠ 0 by
      intro h'
      apply ha
      linarith
    )).mp
    apply (mul_left_inj' (show c ≠ 0 by exact hc1)).mp
    nlinarith [sq_pos_of_ne_zero (show b - a ≠ 0 by intro h' ; apply ha ; linarith),
      sq_pos_of_ne_zero (show c - a ≠ 0 by intro h' ; apply hc ; linarith),
      sq_pos_of_ne_zero (show b ≠ 0 by exact hb1),
      sq_pos_of_ne_zero (show c ≠ 0 by exact hc1)]

  have h3 : r^2 + r - 1 = 0 := eq3
  have h4 : r^2 + r = 1 := by linarith
  have h5 : r = (-1 + Real.sqrt 5) / 2 := by
    have h3' : r^2 + r - 1 = 0 := h3
    have h6 : r^2 + r = 1 := by linarith
    have h7 : r^2 + r - 1 = 0 := h3'
    have h8 : r^2 + r = 1 := by linarith
    have h9 : r^2 + r - 1 = 0 := h3
    have h10 : r = (-1 + Real.sqrt 5) / 2 ∨ r = (-1 - Real.sqrt 5) / 2 := by
      have h2 : r^2 + r - 1 = 0 := h9
      have h3 : r^2 + r - 1 = (r - (-1 + Real.sqrt 5) / 2) * (r - (-1 - Real.sqrt 5) / 2) := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h3] at h2
      cases (mul_eq_zero.1 h2) with
      | inl h4 =>
        left
        linarith
      | inr h5 =>
        right
        linarith
    cases h10 with
    | inl h11 =>
      linarith
    | inr h12 =>
      have h13 : r < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      linarith
  linarith
  all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]