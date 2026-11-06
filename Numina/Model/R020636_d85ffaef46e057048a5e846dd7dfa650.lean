import Mathlib

theorem algebra_276662 {p1 p2 q1 q2 a1 a2 b1 b2 : ℝ}
    (ha1 : a1^2 + p1 * a1 + q1 = 0) (ha2 : a2^2 + p1 * a2 + q1 = 0)
    (hb1 : b1^2 + p2 * b1 + q2 = 0) (hb2 : b2^2 + p2 * b2 + q2 = 0)
    (hne : a1 ≠ a2 ∧ b1 ≠ b2)
    (hroots : ∀ x : ℝ, x^2 + p1 * x + q1 = 0 → x = a1 ∨ x = a2)
    (hroots' : ∀ x : ℝ, x^2 + p2 * x + q2 = 0 → x = b1 ∨ x = b2)
    (h : (b1^2 + p1 * b1 + q1) + (b2^2 + p1 * b2 + q1) =
      (a1^2 + p2 * a1 + q2) + (a2^2 + p2 * a2 + q2)) :
    p1^2 - 4 * q1 = p2^2 - 4 * q2 := by
  have h2 : a1 + a2 = -p1 := by
    have eq1 : a1^2 + p1 * a1 + q1 = 0 := ha1
    have eq2 : a2^2 + p1 * a2 + q1 = 0 := ha2
    have sub_eq : (a1 - a2) * (a1 + a2 + p1) = 0 := by
      linarith
    cases' (mul_eq_zero.mp sub_eq) with h3 h4
    · -- $a1 - a2 = 0$, a contradiction to $a1 \neq a2$
      exfalso
      apply hne.1
      linarith
    · -- $a1 + a2 + p1 = 0$, so $a1 + a2 = -p1$
      linarith
  have h1 : a1 * a2 = q1 := by
    have h3 : a1^2 + a2^2 = p1^2 - 2 * q1 := by
      have h11 : a1^2 + p1 * a1 + q1 = 0 := ha1
      have h12 : a2^2 + p1 * a2 + q1 = 0 := ha2
      have h9 : a1^2 + a2^2 + p1 * (a1 + a2) + 2 * q1 = 0 := by
        nlinarith
      rw [show a1 + a2 = -p1 by linarith [h2]] at h9
      nlinarith
    have h6 : (a1 + a2)^2 = a1^2 + a2^2 + 2 * (a1 * a2) := by
      ring
    rw [show (a1 + a2) = -p1 by linarith [h2]] at h6
    rw [h3] at h6
    nlinarith
  have h3 : b1 + b2 = -p2 := by
    have eq3 : b1^2 + p2 * b1 + q2 = 0 := hb1
    have eq4 : b2^2 + p2 * b2 + q2 = 0 := hb2
    have sub_eq : (b1 - b2) * (b1 + b2 + p2) = 0 := by
      linarith
    cases' (mul_eq_zero.mp sub_eq) with h5 h6
    · -- $b1 - b2 = 0$, a contradiction to $b1 \neq b2$
      exfalso
      apply hne.2
      linarith
    · -- $b1 + b2 + p2 = 0$, so $b1 + b2 = -p2$
      linarith
  have h4 : b1 * b2 = q2 := by
    have h33 : b1^2 + b2^2 = p2^2 - 2 * q2 := by
      have h7 : b1^2 + p2 * b1 + q2 = 0 := hb1
      have h8 : b2^2 + p2 * b2 + q2 = 0 := hb2
      have h9 : b1^2 + b2^2 + p2 * (b1 + b2) + 2 * q2 = 0 := by
        nlinarith
      rw [show b1 + b2 = -p2 by linarith [h3]] at h9
      nlinarith
    have h6 : (b1 + b2)^2 = b1^2 + b2^2 + 2 * (b1 * b2) := by
      ring
    rw [show (b1 + b2) = -p2 by linarith [h3]] at h6
    rw [h33] at h6
    nlinarith
  have h11 : a1^2 + a2^2 = p1^2 - 2 * q1 := by
    have h11 : a1^2 + a2^2 = p1^2 - 2 * q1 := by
      have h11 : a1^2 + p1 * a1 + q1 = 0 := ha1
      have h12 : a2^2 + p1 * a2 + q1 = 0 := ha2
      have h9 : a1^2 + a2^2 + p1 * (a1 + a2) + 2 * q1 = 0 := by
        nlinarith
      rw [show a1 + a2 = -p1 by linarith [h2]] at h9
      nlinarith
    linarith
  have h12 : b1^2 + b2^2 = p2^2 - 2 * q2 := by
    have h12 : b1^2 + b2^2 = p2^2 - 2 * q2 := by
      have h7 : b1^2 + p2 * b1 + q2 = 0 := hb1
      have h8 : b2^2 + p2 * b2 + q2 = 0 := hb2
      have h9 : b1^2 + b2^2 + p2 * (b1 + b2) + 2 * q2 = 0 := by
        nlinarith
      rw [show b1 + b2 = -p2 by linarith [h3]] at h9
      nlinarith
    linarith
  have h5 : (b1^2 + b2^2) + p1 * (b1 + b2) + 2 * q1 = (a1^2 + a2^2) + p2 * (a1 + a2) + 2 * q2 := by
    linarith
  rw [show b1^2 + b2^2 = p2^2 - 2 * q2 by nlinarith, show (b1 + b2) = -p2 by linarith, 
      show a1^2 + a2^2 = p1^2 - 2 * q1 by nlinarith, show (a1 + a2) = -p1 by linarith] at h5
  nlinarith