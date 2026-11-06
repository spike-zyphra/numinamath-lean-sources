import Mathlib

theorem algebra_13981 {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : 1 / a^3 = 512 / b^3) (h2 : 512 / b^3 = 125 / c^3) (h3 : 125 / c^3 = d / (a + b + c)^3) :
    d = 2744 := by
  have eq1 : b^3 = 512 * a^3 := by
    have h1' : 1 / a^3 = 512 / b^3 := h1
    have ha3_pos : 0 < a^3 := by positivity
    have hb3_pos : 0 < b^3 := by positivity
    field_simp at h1' ⊢
    nlinarith [h1']
  have eq2 : b = 8 * a := by
    have h : b^3 = 512 * a^3 := eq1
    have h1 : b^3 - 512 * a^3 = 0 := by linarith
    have h2 : b^3 - 512 * a^3 = (b - 8 * a) * (b^2 + 8 * a * b + 64 * a^2) := by
      ring_nf
    rw [h2] at h1
    cases' (mul_eq_zero.1 h1) with h3 h4
    · linarith
    · -- Now we need to show that the quadratic factor is non zero for positive a, b
      have h5 : b^2 + 8 * a * b + 64 * a^2 > 0 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb, sq_nonneg (b - 8 * a)]
      linarith [h5, show b^2 + 8 * a * b + 64 * a^2 ≥ 0 by nlinarith]
  have eq3 : c^3 = 125 * a^3 := by
    have h2' : 512 / b^3 = 125 / c^3 := h2
    rw [show b^3 = 512 * a ^ 3 by linarith [eq1]] at h2'
    have ha3_pos : 0 < a^3 := by positivity
    have hc3_pos : 0 < c^3 := by positivity
    field_simp at h2' ⊢
    nlinarith [h2', ha3_pos, hc3_pos]
  have eq4 : c = 5 * a := by
    have h5 : c^3 - 125 * a^3 = 0 := by
      linarith [eq3]
    have h6 : c^3 - 125 * a^3 = (c - 5 * a) * (c^2 + 5 * a * c + 25 * a^2) := by
      ring_nf
    rw [h6] at h5
    cases' (mul_eq_zero.1 h5) with h7 h8
    · -- Case where c - 5 * a = 0
      linarith
    · -- Now we need to show that the quadratic factor is non zero for positive a, c
      have h5 : c^2 + 5 * a * c + 25 * a^2 > 0 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hc, mul_pos ha hc, sq_nonneg (c - 5 * a)]
      linarith [h5, show c^2 + 5 * a * c + 25 * a^2 ≥ 0 by nlinarith]
  have eq5 : a + b + c = 14 * a := by
    nlinarith [eq2, eq4]
  have eq6 : (a + b + c) ^ 3 = 2744 * a^3 := by
    rw [eq5]
    ring_nf
  have eq7 : d = 2744 := by
    have h3' : 125 / c^3 = d / (a + b + c) ^ 3 := h3
    rw [show c ^ 3 = 125 * a ^ 3 by linarith [eq3], eq6] at h3'
    have ha3_pos : 0 < a^3 := by positivity
    field_simp at h3' ⊢
    nlinarith [h3', sq_pos_of_pos ha, sq_pos_of_pos hd, mul_pos ha hd]
  linarith [eq7]