import Mathlib

theorem algebra_1341
    (a b c : ℝ)
    (h₀ : a > 0)
    (h₁ : b > 0)
    (h₂ : c > 0)
    (h₃ : a + b > c)
    (h₄ : a + c > b)
    (h₅ : b + c > a)
    (h₆ : a^2 - 9 * a + 18 = 0)
    (h₇ : b^2 - 9 * b + 18 = 0)
    (h₈ : c^2 - 9 * c + 18 = 0) :
    a + b + c = 9 ∨ a + b + c = 15 ∨ a + b + c = 18 := by

  have ha : (a - 3) * (a - 6) = 0 := by
    linarith

  have hb : (b - 3) * (b - 6) = 0 := by
    linarith

  have hc : (c - 3) * (c - 6) = 0 := by
    linarith

  have ha3 : a = 3 ∨ a = 6 := by
    cases (mul_eq_zero.mp ha) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith

  have hb3 : b = 3 ∨ b = 6 := by
    cases (mul_eq_zero.mp hb) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith

  have hc3 : c = 3 ∨ c = 6 := by
    cases (mul_eq_zero.mp hc) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith

  rcases ha3 with ha3 | ha6
  · rcases hb3 with hb3 | hb6
    · rcases hc3 with hc3 | hc6
      · -- a = 3, b = 3, c = 3
        have h9 : a + b + c = 9 := by
          linarith
        left
        exact h9
      · -- a = 3, b = 3, c = 6
        exfalso
        rw [show a = 3 by linarith [ha3], show b = 3 by linarith [hb3], show c = 6 by linarith [hc6]] at h₃
        norm_num at h₃
    · rcases hc3 with hc3 | hc6
      · -- a = 3, b = 6, c = 3
        exfalso
        rw [show a = 3 by linarith [ha3], show b = 6 by linarith [hb6], show c = 3 by linarith [hc3]] at h₄
        norm_num at h₄
      · -- a = 3, b = 6, c = 6
        have h15 : a + b + c = 15 := by
          linarith
        right
        left
        exact h15
  · rcases hb3 with hb3 | hb6
    · rcases hc3 with hc3 | hc6
      · -- a = 6, b = 3, c = 3
        exfalso
        rw [show a = 6 by linarith [ha6], show b = 3 by linarith [hb3], show c = 3 by linarith [hc3]] at h₅
        norm_num at h₅
      · -- a = 6, b = 3, c = 6
        have h15 : a + b + c = 15 := by
          linarith
        right
        left
        exact h15
    · rcases hc3 with hc3 | hc6
      · -- a = 6, b = 6, c = 3
        have h15 : a + b + c = 15 := by
          linarith
        right
        left
        exact h15
      · -- a = 6, b = 6, c = 6
        have h18 : a + b + c = 18 := by
          linarith
        right
        right
        exact h18