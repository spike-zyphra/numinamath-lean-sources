import Mathlib

theorem algebra_310651 {p1 p2 q1 q2 a1 a2 b1 b2 : ℝ}
    (ha1 : a1^2 + p1 * a1 + q1 = 0) (ha2 : a2^2 + p1 * a2 + q1 = 0)
    (hb1 : b1^2 + p2 * b1 + q2 = 0) (hb2 : b2^2 + p2 * b2 + q2 = 0)
    (hne : a1 ≠ a2 ∧ b1 ≠ b2)
    (h : (b1^2 + p1 * b1 + q1) + (b2^2 + p1 * b2 + q1) =
      (a1^2 + p2 * a1 + q2) + (a2^2 + p2 * a2 + q2)) :
    p1^2 - 4 * q1 = p2^2 - 4 * q2 := by

  have h1 : a1 + a2 = -p1 := by
    have h_eq : (a1 - a2) * (a1 + a2 + p1) = 0 := by
      nlinarith
    have h2 : a1 - a2 ≠ 0 := by
      intro h'
      apply hne.1
      linarith
    have h3 : a1 + a2 + p1 = 0 := by
      apply (mul_right_inj' h2).mp
      linarith
    linarith

  have h3 : b1 + b2 = -p2 := by
    have h_eq : (b1 - b2) * (b1 + b2 + p2) = 0 := by
      nlinarith
    have h4 : b1 - b2 ≠ 0 := by
      intro h'
      apply hne.2
      linarith
    have h5 : b1 + b2 + p2 = 0 := by
      apply (mul_right_inj' h4).mp
      linarith
    linarith

  have h6 : a1 * a2 = q1 := by
    have h_eq2 : a1^2 + p1 * a1 + q1 = 0 := by linarith [ha1]
    have h_eq3 : a2^2 + p1 * a2 + q1 = 0 := by linarith [ha2]
    have h_eq4 : a1 + a2 = -p1 := by linarith [h1]
    have eq3 : a1^2 + a2^2 + p1 * (a1 + a2) + 2 * q1 = 0 := by
      nlinarith
    rw [show a1 + a2 = -p1 by linarith [h1] ] at eq3
    have eq4 : (a1 + a2)^2 = a1^2 + a2^2 + 2 * (a1 * a2) := by ring
    rw [show a1 + a2 = -p1 by linarith [h1] ] at eq4
    nlinarith

  have h7 : b1 * b2 = q2 := by
    have h_eq2 : b1^2 + p2 * b1 + q2 = 0 := by linarith [hb1]
    have h_eq3 : b2^2 + p2 * b2 + q2 = 0 := by linarith [hb2]
    have h_eq4 : b1 + b2 = -p2 := by linarith [h3]
    have eq5 : b1^2 + b2^2 + p2 * (b1 + b2) + 2 * q2 = 0 := by
      nlinarith
    rw [show b1 + b2 = -p2 by linarith [h3] ] at eq5
    have eq6 : (b1 + b2)^2 = b1^2 + b2^2 + 2 * (b1 * b2) := by ring
    rw [show b1 + b2 = -p2 by linarith [h3] ] at eq6
    nlinarith

  have eq1 : b1 ^ 2 + b2 ^ 2 + p1 * (b1 + b2) + 2 * q1 = a1^2 + a2^2 + p2 * (a1 + a2) + 2 * q2 := by
    have eq7 : (b1^2 + p1 * b1 + q1) + (b2^2 + p1 * b2 + q1) =
      (a1^2 + p2 * a1 + q2) + (a2^2 + p2 * a2 + q2) := by linarith [h]
    nlinarith

  have eq5 : p1 ^ 2 - 4 * q1 = p2 ^ 2 - 4 * q2 := by 
    rw [show b1 + b2 = -p2 by linarith [h3], show a1 + a2 = -p1 by linarith [h1] ] at eq1 
    nlinarith [sq_pos_of_ne_zero (show (a1 - a2) ≠ 0 by intro h'; apply hne.1; linarith), sq_pos_of_ne_zero (show (b1 - b2) ≠ 0 by intro h'; apply hne.2; linarith), 
      h6, h7, sq_nonneg (a1 - a2), sq_nonneg (b1 - b2)]

  exact_mod_cast eq5