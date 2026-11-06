import Mathlib

theorem algebra_245228 (p q a b c : ℝ) (hp : 0 < p) (hq : 0 < q)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hne : p ≠ q)
    (hge : ∃ r, a = r * p ∧ q = r * a) (har : ∃ d, b = d + p ∧ c = d + b ∧ q = d + c) :
    ¬∃ x : ℝ, b * x ^ 2 - 2 * a * x + c = 0 := by
  rcases hge with ⟨r, h1, h2⟩
  have ha2 : a = r * p := by linarith
  have hq2 : q = r ^ 2 * p := by 
    rw [h1] at h2 
    linarith
  have h3 : r ^ 2 = q / p := by
    have hpne : p ≠ 0 := by linarith
    field_simp
    nlinarith 
  rcases har with ⟨d, h4, h5, h6⟩ 
  have h7 : b = (2 * p + q) / 3 := by
    nlinarith [h4, h5, h6]
  have h8 : c = (p + 2 * q) / 3 := by
    nlinarith [h4, h5, h6, h7]
  have eq1 : a ^ 2 = p * q := by 
    nlinarith [h1, ha2, hq2, h3, mul_pos hp hq]
  have h11 : 4 * a ^ 2 - 4 * b * c < 0 := by 
    have eq2 : a ^ 2 = p * q := eq1 
    have h12 : b * c = ((2 * p + q) * (p + 2 * q)) / 9 := by 
      rw [h7, h8]
      nlinarith 
    have eq3 : 4 * a ^ 2 - 4 * b * c = (4 * (p * q) - 4 * ((2 * p + q) * (p + 2 * q)) / 9 ) := by 
      have eq4 : a ^ 2 = p * q := eq1 
      have eq5 : b * c = ((2 * p + q) * (p + 2 * q)) / 9 := h12 
      linarith [eq4, eq5] 
    rw [eq3] 
    nlinarith [sq_pos_of_ne_zero (show (p - q) ≠ 0 by 
        intro h 
        apply hne 
        nlinarith 
    ), sq_pos_of_pos hp, sq_pos_of_pos hq, mul_pos hp hq]
  intro h 
  rcases h with ⟨x, hx⟩ 
  have h14 : b * x ^ 2 - 2 * a * x + c = 0 := hx 
  have h15 : (4 * a ^ 2 - 4 * b * c) ≥ 0 := by 
    nlinarith [sq_nonneg (b * x - a), sq_nonneg (x * (b) - a), sq_nonneg (b * x ^ 2 - 2 * a * x + c), sq_nonneg (2 * a - 2 * b * x), sq_nonneg (b - a / x), sq_pos_of_pos hp, sq_pos_of_pos hq, mul_pos hp hq]
  nlinarith