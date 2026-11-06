import Mathlib

theorem algebra_3181 {a b d : ℝ} (hroots : a ≠ b ∧ a^2+d*a+12=0∧ b^2+d*b+12=0) : a^3+b^3=-d^3+36*d:= by
  have h1 : a^2 + d * a + 12 = 0 := by
    exact hroots.right.left
  have h2 : b^2 + d * b + 12 = 0 := by
    exact hroots.right.right
  have h3 : a + b = -d := by
    have h4 : a^2 + d * a + 12 - (b^2 + d * b + 12) = 0 := by
      linarith
    have h5 : (a - b) * (a + b + d) = 0 := by
      ring_nf at h4 ⊢
      linarith
    cases (mul_eq_zero.mp h5) with
    | inl h6 =>
      exfalso
      apply hroots.left 
      linarith 
    | inr h7 =>
      linarith
  have h8 : a * b = 12 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by intro h; apply hroots.left; linarith), h3]
  have h9 : a^3 + b^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by
    ring_nf
  rw [h9, h3, h8]
  ring_nf