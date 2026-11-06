import Mathlib

theorem algebra_236512 {a b c : ℝ} (h1 : a^3 + 3 * a * b^2 + 3 * a * c^2 - 6 * a * b * c = 1)
(h2 : b^3 + 3 * b * a^2 + 3 * b * c^2 - 6 * a * b * c = 1) (h3 : c^3 + 3 * c * a^2 + 3 * c * b^2 - 6 * a * b * c = 1) :
(a, b, c) = (1, 1, 1) := by
  have h4 : (a - b) * ((a - b) ^ 2 + 3 * c ^ 2) = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h5 : (b - c) * ((b - c) ^ 2 + 3 * a ^ 2) = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  cases (mul_eq_zero.mp h4) with
  | inl h4 =>
    have hab : a = b := by linarith
    cases (mul_eq_zero.mp h5) with
    | inl h5 =>
      have hbc : b = c := by linarith
      have hac : a = c := by linarith [hab, hbc]
      have ha1 : a = 1 := by
        have h1' : a^3 = 1 := by
          rw [show b = a by linarith [hab], show c = a by linarith [hac]] at h1
          nlinarith [sq_nonneg (a - 1), sq_nonneg (a^2 - 1)]
        have h1 : a^3 - 1 = 0 := by linarith
        have h1 : (a - 1) * (a^2 + a + 1) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h1) with
        | inl h1 =>
          linarith
        | inr h1 =>
          have h2 : a^2 + a + 1 = 0 := by linarith
          nlinarith [sq_nonneg (a + 1 / 2)]
      have hb1 : b = 1 := by linarith [hab, ha1]
      have hc1 : c = 1 := by linarith [hac, ha1]
      simp [ha1, hb1, hc1]
    | inr h5 =>
      have h5' : (b - c) ^ 2 + 3 * a ^ 2 = 0 := by
        linarith
      have hbc : b = c := by
        nlinarith [sq_nonneg (b - c), sq_nonneg (a), sq_nonneg (c)]
      have ha0 : a = 0 := by
        nlinarith [sq_nonneg (a), sq_nonneg (b - c), sq_nonneg (c), h5']
      have hb0 : b = 0 := by linarith [hab, ha0]
      have hc0 : c = 0 := by linarith [hbc, hb0]
      nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), sq_nonneg (c - 0)]
  | inr h4 =>
    have h4' : (a - b) ^ 2 + 3 * c ^ 2 = 0 := by
      linarith
    have hab : a = b := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (c)]
    have hc0 : c = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (c)]
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 0), sq_nonneg (a^2 - 1 / 4)]