import Mathlib

theorem inequalities_75556 (a b c d e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (h1 : ∃ d' : ℝ, b = a + d' ∧ c = b + d' ∧ d = c + d')
    (h2 : ∃ r : ℝ, e = a * r ∧ f = e * r ∧ d = f * r) :
    b * c ≥ e * f := by
  rcases h1 with ⟨d', h11, h12, h13⟩
  rcases h2 with ⟨r, h21, h22, h23⟩

  have eq1 : b = a + d' := by linarith
  have eq2 : c = a + 2 * d' := by 
    have h3 : c = b + d' := by linarith
    rw [h3, eq1]
    all_goals linarith

  have eq3 : d = a + 3 * d' := by
    have h4 : d = c + d' := by linarith
    rw [h4, eq2]
    all_goals linarith

  have eq4 : e = a * r := by linarith

  have eq5 : f = a * r ^ 2 := by 
    have h6 : f = e * r := by linarith
    rw [h6, eq4]
    all_goals ring

  have eq6 : d = a * r ^ 3 := by 
    have h7 : d = f * r := by linarith
    rw [h7, eq5]
    all_goals ring

  have eq7 : a + 3 * d' = a * r ^ 3 := by
    linarith [eq3, eq6]

  have eq8 : b * c = (a + d') * (a + 2 * d') := by
    rw [eq1, eq2]

  have eq9 : e * f = (a * r) * (a * r ^ 2) := by 
    rw [eq4, eq5]

  have eq10 : e * f = a ^ 2 * r ^ 3 := by
    rw [eq9]
    all_goals ring
  
  nlinarith [sq_nonneg (a * r ^ 2 - (a + d')), sq_nonneg (r - 1), sq_nonneg (d'), sq_nonneg (a - 0), sq_nonneg (d' - 0), mul_pos ha hb, mul_pos hb hc, mul_pos hc hd, mul_pos ha he, mul_pos he hf, mul_pos hb he, mul_pos hc hf, mul_pos hd ha, mul_pos hd hb, mul_pos hd hc, mul_pos hd he, mul_pos hd hf]