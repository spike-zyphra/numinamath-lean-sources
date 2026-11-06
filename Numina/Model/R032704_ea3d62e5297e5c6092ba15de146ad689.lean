import Mathlib

theorem algebra_207207 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : 1 / a^3 = 512 / b^3) (h2 : 1 / a^3 = 125 / c^3) (h3 : 512 / b^3 = d / (a + b + c)^3) :
    d = 2744 := by

  have eq1 : b^3 = 512 * a^3 := by
    field_simp at h1
    nlinarith [h1, mul_pos ha hb]

  have eq2 : c^3 = 125 * a^3 := by
    field_simp at h2
    nlinarith [h2, mul_pos ha hc]

  have eq3 : b = 8 * a := by
    have h4 : b^3 - 512 * a^3 = 0 := by linarith
    have h5 : b^3 - 512 * a^3 = (b - 8 * a) * (b^2 + 8 * a * b + 64 * a^2) := by 
      ring
    rw [h5] at h4
    cases (mul_eq_zero.mp h4) with
    | inl h6 => linarith
    | inr h7 =>
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb]

  have eq4 : c = 5 * a := by
    have h6 : c^3 - 125 * a^3 = 0 := by linarith
    have h7 : c^3 - 125 * a^3 = (c - 5 * a) * (c^2 + 5 * a * c + 25 * a^2) := by 
      ring
    rw [h7] at h6
    cases (mul_eq_zero.mp h6) with
    | inl h8 => linarith
    | inr h9 =>
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hc, mul_pos ha hc]

  have eq5 : a + b + c = 14 * a := by
    rw [show b = 8 * a by linarith [eq3], show c = 5 * a by linarith [eq4]]
    linarith

  have eq6 : (a + b + c)^3 = 2744 * a^3 := by
    rw [eq5]
    have h7 : (14 * a)^3 = 2744 * a^3 := by
      ring_nf
    nlinarith [h7, sq_pos_of_pos ha]

  have eq8 : 512 / b^3 = 1 / a^3 := by 
    have h9 : b^3 = 512 * a^3 := eq1
    field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith] at *
    nlinarith

  have eq9 : d / (a + b + c)^3 = 1 / a^3 := by
    linarith [h3, eq8]

  have eq10 : d * a^3 = (a + b + c)^3 := by
    have h11 : d / (a + b + c)^3 = 1 / a^3 := eq9
    have h12 : a ≠ 0 := by linarith
    have h13 : a + b + c ≠ 0 := by
      nlinarith [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith]
    field_simp [h13, h12] at h11 ⊢
    nlinarith [h11, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have eq11 : (a + b + c)^3 = 2744 * a^3 := eq6
  rw [eq11] at eq10

  have h14 : a^3 > 0 := by
    positivity

  have h15 : d = 2744 := by
    nlinarith [eq10, h14]

  exact h15