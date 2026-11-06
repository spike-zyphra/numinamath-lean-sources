import Mathlib

theorem algebra_6498 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (f : ℝ → ℝ)
(h : ∀ x, f x = x ^ 4 - 11 * x ^ 3 + 36 * x ^ 2 - 36 * x) (h1 : f a = 0)
(h2 : f b = 0) (h3 : a + b > 8) (h4 : a ≠ b) :
a + b = 9 := by
  have h1' : a ^ 4 - 11 * a ^ 3 + 36 * a ^ 2 - 36 * a = 0 := by
    rw [h] at h1
    exact h1
  have h2' : b ^ 4 - 11 * b ^ 3 + 36 * b ^ 2 - 36 * b = 0 := by
    rw [h] at h2
    exact h2
  have h1'' : a * (a ^ 3 - 11 * a ^ 2 + 36 * a - 36) = 0 := by
    nlinarith [h1']
  have h1cubic : (a - 2) * (a - 3) * (a - 6) = 0 := by
    cases' (mul_eq_zero.1 h1'') with ha1 ha2
    · -- Suppose a = 0
      nlinarith
    · -- So c^3 - 11c^2 + 36c - 36 = 0
      nlinarith [ha2]
  have h2'' : b * (b ^ 3 - 11 * b ^ 2 + 36 * b - 36) = 0 := by
    nlinarith [h2']
  have h2cubic : (b - 2) * (b - 3) * (b - 6) = 0 := by
    cases' (mul_eq_zero.1 h2'') with hb1 hb2
    · -- Suppose b = 0
      nlinarith
    · -- So c^3 - 11c^2 + 36c - 36 = 0
      nlinarith [hb2]

  have ha2 : a = 2 ∨ a = 3 ∨ a = 6 := by
    cases (mul_eq_zero.1 h1cubic) with
    | inl h5 =>
      cases (mul_eq_zero.1 h5) with
      | inl h6 =>
        left
        linarith
      | inr h7 =>
        right
        left
        linarith
    | inr h8 =>
      right
      right
      linarith

  have hb2 : b = 2 ∨ b = 3 ∨ b = 6 := by
    cases (mul_eq_zero.1 h2cubic) with
    | inl h5 =>
      cases (mul_eq_zero.1 h5) with
      | inl h6 =>
        left
        linarith
      | inr h7 =>
        right
        left
        linarith
    | inr h8 =>
      right
      right
      linarith

  rcases ha2 with ha2 | ha3 | ha6
  · rcases hb2 with hb2 | hb3 | hb6
    · -- a = 2, b = 2
      exfalso
      apply h4
      linarith
    · -- a = 2, b = 3
      nlinarith
    · -- a = 2, b = 6
      nlinarith
  · rcases hb2 with hb2 | hb3 | hb6
    · -- a = 3, b = 2
      nlinarith
    · -- a = 3, b = 3
      exfalso
      apply h4
      linarith
    · -- a = 3, b = 6
      nlinarith
  · rcases hb2 with hb2 | hb3 | hb6
    · -- a = 6, b = 2
      nlinarith
    · -- a = 6, b = 3
      nlinarith
    · -- a = 6, b = 6
      exfalso
      apply h4
      linarith
  all_goals
    nlinarith
    <;> tauto
  all_goals
    nlinarith
    <;> tauto