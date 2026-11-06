import Mathlib

theorem algebra_141705 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (h₀ : |(4 * a - 4 * b)| = 8) (h₁ : |(a^2 - b^2)| = 16) :
    a^2 + b^2 = 34 := by 
  cases eq_or_eq_neg_of_abs_eq h₀ with
  | inl h2 =>
    have h2' : a - b = 2 := by
      linarith
    cases eq_or_eq_neg_of_abs_eq h₁ with
    | inl h3 =>
      have h3' : a^2 - b^2 = 16 := by
        linarith
      have h4 : a + b = 8 := by
        have h5 : a^2 - b^2 = (a - b) * (a + b) := by ring
        rw [h5] at h3'
        rw [h2'] at h3'
        linarith
      have ha1 : a = 5 := by
        linarith [h2', h4]
      have hb1 : b = 3 := by
        linarith [h2', ha1]
      nlinarith [ha1, hb1]
    | inr h3 =>
      have h3' : b^2 - a^2 = 16 := by
        linarith
      have h4 : a + b > 0 := by
        nlinarith
      have h5 : b^2 - a^2 = (b - a) * (a + b) := by ring
      rw [h5] at h3'
      have h6 : b - a = -2 := by
        linarith [h2']
      rw [h6] at h3'
      nlinarith
  | inr h2 =>
    have h2' : b - a = 2 := by
      linarith
    cases eq_or_eq_neg_of_abs_eq h₁ with
    | inl h3 =>
      have h3' : a^2 - b^2 = 16 := by
        linarith
      have h4 : a + b > 0 := by
        nlinarith
      have h5 : a^2 - b^2 = (a - b) * (a + b) := by ring
      rw [h5] at h3'
      have h6 : a - b = -2 := by
        linarith [h2']
      rw [h6] at h3'
      nlinarith
    | inr h3 =>
      have h3' : b^2 - a^2 = 16 := by
        linarith
      have h4 : b + a = 8 := by
        have h5 : b^2 - a^2 = (b - a) * (b + a) := by ring
        rw [h5] at h3'
        rw [h2'] at h3'
        linarith
      have hb1 : b = 5 := by
        linarith [h2', h4]
      have ha1 : a = 3 := by
        linarith [h2', hb1]
      nlinarith [ha1, hb1]