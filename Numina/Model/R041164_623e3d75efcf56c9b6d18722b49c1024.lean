import Mathlib

theorem algebra_314806 {p q a b c : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hne : p ≠ q) (hge : ∃ r, p * r = a ∧ a * r = q)
    (har : ∃ d, p + d = b ∧ b + d = c ∧ c + d = q) :
    ¬∃ x : ℝ, b * x ^ 2 - 2 * a * x + c = 0 := by
  rcases hge with ⟨r, h1, h2⟩
  have h3 : a ^ 2 = p * q := by
    have h4 : a = p * r := by linarith
    have h5 : q = a * r := by linarith
    rw [h4] at h5
    have h6 : q = (p * r) * r := by linarith
    have h7 : q = p * (r ^ 2) := by
      ring_nf at h6 ⊢
      linarith
    nlinarith [h4, h7]
  rcases har with ⟨d, h8, h9, h10⟩
  have h11 : b = p + d := by linarith
  have h12 : c = b + d := by linarith
  have h13 : c = p + 2 * d := by 
    nlinarith [h11, h12]
  have h14 : q = c + d := by linarith
  have h15 : q = p + 3 * d := by 
    nlinarith [h13, h14]
  have h16 : b * c > a ^ 2 := by
    have h17 : a ^ 2 = p * q := h3
    rw [h17] at *
    have hd : d = (q - p) / 3 := by
      nlinarith [h15]
    have hb' : b = (2 * p + q) / 3 := by
      nlinarith [h11, hd]
    have hc' : c = (p + 2 * q) / 3 := by
      nlinarith [h13, hd]
    rw [hb', hc']
    have h18 : (q - p) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      intro h'
      apply hne
      linarith
    nlinarith [sq_pos_of_ne_zero (show (p - q) ≠ 0 by
      intro h'
      apply hne
      linarith
    ), sq_nonneg (p - q), sq_nonneg (p + q), mul_pos hp hq, sq_pos_of_pos hp, sq_pos_of_pos hq]
  intro h
  rcases h with ⟨x, hx⟩
  have h18 : (2 * a) ^ 2 < 4 * b * c := by
    nlinarith [h16, mul_pos hp hq, mul_pos hp ha, mul_pos hq ha, mul_pos hb hc]
  have h19 : b * x ^ 2 - 2 * a * x + c = 0 := by 
    linarith
  have h20 : (2 * b * x - 2 * a) ^ 2 < 0 := by 
    nlinarith [sq_nonneg (2 * b * x - 2 * a), h18, h19, mul_pos hb ha, mul_pos hb hc, mul_pos ha hq, mul_pos hp hq, sq_nonneg (x * b - a)]
  have h21 : (2 * b * x - 2 * a) ^ 2 ≥ 0 := by
    apply sq_nonneg
  linarith