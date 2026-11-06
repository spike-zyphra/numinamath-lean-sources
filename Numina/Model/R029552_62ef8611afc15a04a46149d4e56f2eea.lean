import Mathlib

theorem algebra_13138 {a b c d : ℝ} (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : c^2 - 10*a*c - 11*b = 0) (h2 : d^2 - 10*a*d - 11*b = 0)
    (h3 : a^2 - 10*c*a - 11*d = 0) (h4 : b^2 - 10*c*b - 11*d = 0) :
    a + b + c + d = 1210 := by 
  have eq1 : c + d = 10 * a := by 
    have h5 : c^2 - 10 * a * c - 11 * b = 0 := h1
    have h6 : d^2 - 10 * a * d - 11 * b = 0 := h2
    have h7 : c^2 - d^2 - 10 * a * c + 10 * a * d = 0 := by
      nlinarith [h5, h6]
    have h8 : c ≠ d := hf
    have h9 : (c - d) * (c + d - 10 * a) = 0 := by
      ring_nf at h7 ⊢
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- c - d = 0
      exfalso
      apply hf
      linarith
    · -- c + d - 10 a = 0
      linarith
  have eq2 : a + b = 10 * c := by
    have h7 : a^2 - 10 * c * a - 11 * d = 0 := h3
    have h8 : b^2 - 10 * c * b - 11 * d = 0 := h4
    have h9 : a^2 - b^2 - 10 * c * a + 10 * c * b = 0 := by
      nlinarith [h7, h8]
    have h10 : a ≠ b := ha
    have h11 : (a - b) * (a + b - 10 * c) = 0 := by
      ring_nf at h9 ⊢
      nlinarith
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- a - b = 0
      exfalso
      apply ha
      linarith
    · -- a + b - 10 c = 0
      linarith
  have h5 : b = 10 * c - a := by 
    linarith [eq2]
  have h6 : d = 10 * a - c := by
    linarith [eq1]
  rw [show b = 10 * c - a by linarith [eq2]] at h1
  rw [show d = 10 * a - c by linarith [eq1]] at h3
  have h9 : a + c = 121 := by 
    nlinarith [sq_pos_of_ne_zero (show c - d ≠ 0 by
      intro h'
      apply hf
      linarith
    ), sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h'
      apply ha
      linarith
    ), sq_pos_of_ne_zero (show a - c ≠ 0 by
      intro h'
      apply hb
      linarith
    )]
  have h10 : a + b + c + d = 10 * (a + c) := by
    nlinarith [eq1, eq2]
  nlinarith [h9, h10]