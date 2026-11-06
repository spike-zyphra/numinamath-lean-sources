import Mathlib

theorem algebra_326941 {a b c d : ℝ} (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : (b + d) * (b + a) = 1) (h2 : (c + d) * (c + a) = 1) :
    (b + d) * (c + d) = -1 := by
  have h3 : (b + d) * (b + a) - (c + d) * (c + a) = 0 := by linarith
  have h4 : (b + d) * (b + a) - (c + d) * (c + a) = (b - c) * (b + c + a + d) := by
    ring
  rw [h4] at h3
  cases (mul_eq_zero.1 h3) with
  | inl h5 =>
    exfalso
    apply hd
    linarith
  | inr h5 =>
    have h6 : b + c + a + d = 0 := by linarith
    have h7 : (b + d) * (c + d) = -1 := by
      have h8 : b + d = - (a + c) := by
        linarith
      rw [h8]
      have h9 : (c + a) * (c + d) = 1 := by
        nlinarith
      have h10 : (a + c) * (c + d) = 1 := by
        nlinarith
      nlinarith
    linarith [h7]