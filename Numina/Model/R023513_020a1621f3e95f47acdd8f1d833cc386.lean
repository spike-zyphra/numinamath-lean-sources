import Mathlib

theorem algebra_323041 {x1 x2 a : ℝ} (hx1 : x1^2 + (3 * a - 1) * x1 + 2 * a^2 - 1 = 0)
    (hx2 : x2^2 + (3 * a - 1) * x2 + 2 * a^2 - 1 = 0) (hroots : x1 ≠ x2)
    (hdiff : (3 * x1 - x2) * (x1 - 3 * x2) = -80) :
    a = -33 / 5 := by

  have h1 : x1 + x2 = 1 - 3 * a := by
    have h2 : x1^2 + (3 * a - 1) * x1 + 2 * a^2 - 1 - (x2^2 + (3 * a - 1) * x2 + 2 * a^2 - 1) = 0 := by
      linarith [hx1, hx2]
    have h3 : (x1 - x2) * (x1 + x2 + 3 * a - 1) = 0 := by
      ring_nf at h2 ⊢
      <;> linarith 
    cases (mul_eq_zero.mp h3) with
    | inl h4 =>
      exfalso
      apply hroots
      linarith 
    | inr h5 =>
      linarith

  have h2 : x1 * x2 = 2 * a^2 - 1 := by
    have hx2_sub : x2 = (1 - 3 * a) - x1 := by 
      linarith [h1]
    rw [hx2_sub]
    nlinarith [hx1]

  have h3 : 5 * a^2 + 18 * a - 99 = 0 := by
    have eq1 : (x1 + x2) = 1 - 3 * a := h1 
    have eq2 : x1 * x2 = 2 * a^2 - 1 := h2
    have eq3 : x1^2 + x2^2 = 3 - 6 * a + 5 * a^2 := by
      nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by
        intro h
        apply hroots
        linarith 
      ), h1, h2]
    have h4 : (3 * x1 - x2) * (x1 - 3 * x2) = 3 * (x1^2 + x2^2) - 10 * (x1 * x2) := by
      nlinarith 
    rw [h4] at hdiff 
    rw [eq3, eq2] at hdiff 
    nlinarith

  have h4 : (a - 3) * (a + 33 / 5) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- a = 3
    have ha3 : a = 3 := by linarith 
    rw [ha3] at hx1 hx2 
    have h5 : (x1 - x2)^2 < 0 := by 
      nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by
        intro h
        apply hroots
        linarith 
      ), sq_nonneg (x1 + 4), sq_nonneg (x2 + 4)]
    have h6 : (x1 - x2)^2 ≥ 0 := by 
      apply sq_nonneg 
    linarith 
  · -- a = -33/5
    linarith