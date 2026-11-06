import Mathlib

theorem algebra_315894 (p q a b c : ℝ) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hne : p ≠ q) (hge : ∃ r, p * r = a ∧ a * r = q)
    (har : ∃ d, p + d = b ∧ b + d = c ∧ c + d = q) :
    ¬∃ x : ℝ, b * x ^ 2 - 2 * a * x + c = 0 := by
  rcases hge with ⟨r, h1, h2⟩
  have h3 : a ^ 2 = p * q := by 
    have eq1 : p * r = a := by linarith
    have eq2 : a * r = q := by linarith
    have eq3 : r = a / p := by 
      field_simp
      linarith
    rw [eq3] at eq2
    field_simp at eq2
    nlinarith
  rcases har with ⟨d, h4, h5, h6⟩
  have h7 : b = p + d := by linarith
  have h8 : c = p + 2 * d := by
    nlinarith [h4, h5]
  have h9 : q = p + 3 * d := by
    nlinarith [h4, h5, h6]
  have hdne : d ≠ 0 := by
    by_contra h
    have h10 : q = p := by 
      nlinarith [h9, h]
    have h11 : p = q := by 
      linarith [h10]
    contradiction
  intro h
  rcases h with ⟨x, hx⟩
  have h10 : b * x ^ 2 - 2 * a * x + c = 0 := hx
  have h11 : a ^ 2 = p * q := h3
  have h12 : b = p + d := h7
  have h13 : c = p + 2 * d := h8
  have h14 : q = p + 3 * d := h9
  have h15 : a ^ 2 = p * (p + 3 * d) := by
    have h16 : q = p + 3 * d := h9
    rw [h16] at h11
    linarith
  have h16 : b * c = (p + d) * (p + 2 * d) := by 
    rw [h12, h13]
  have h17 : a ^ 2 - (b * c) = -2 * (d ^ 2) := by
    rw [h15, h16]
    nlinarith
  have h18 : a ^ 2 - (b * c) < 0 := by
    have hd2 : d ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      exact hdne
    nlinarith
  have h19 : (2 * b * x - 2 * a) ^ 2 = 4 * (a ^ 2 - (b * c)) := by 
    nlinarith [h10]
  have h20 : (2 * b * x - 2 * a) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h21 : 4 * (a ^ 2 - (b * c)) < 0 := by 
    linarith [h18]
  nlinarith [h19, h20, h21]