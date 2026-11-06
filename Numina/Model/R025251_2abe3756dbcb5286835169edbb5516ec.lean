import Mathlib

theorem algebra_326208 (p q a b c : ℝ) (hp : 0 < p) (hq : 0 < q) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hne : p ≠ q) (hge : ∃ r, a = r * p ∧ q = r * a)
    (har : ∃ d, b = d + p ∧ c = d + b ∧ q = d + c) :
    ¬∃ x : ℝ, b * x ^ 2 - 2 * a * x + c = 0 := by
  rcases hge with ⟨r, ha1, hq1⟩
  rcases har with ⟨d, hb1, hc1, hq2⟩
  have h1 : a ^ 2 = p * q := by
    have ha11 : a = r * p := by linarith [ha1]
    have hq11 : q = r * a := by linarith [hq1]
    rw [ha11] at hq11
    nlinarith [sq_pos_of_pos hp, sq_pos_of_pos hq, sq_pos_of_ne_zero (show p ≠ 0 by linarith [hp]), sq_pos_of_ne_zero (show q ≠ 0 by linarith [hq]), hne, ha11]
  have h2 : b = (2 * p + q) / 3 := by
    nlinarith
  have h3 : c = (p + 2 * q) / 3 := by
    nlinarith [hb1, hc1, hq2, h2]
  intro h
  rcases h with ⟨x, hx⟩
  have h4 : (4 * a ^ 2 - 4 * b * c) < 0 := by
    nlinarith [h1, h2, h3, sq_pos_of_pos hp, sq_pos_of_pos hq, sq_pos_of_ne_zero (show p - q ≠ 0 by intro h11; apply hne; linarith), sq_nonneg (p - q)]
  have h5 : (4 * a ^ 2 - 4 * b * c) ≥ 0 := by
    nlinarith [sq_nonneg (b * x - a), sq_nonneg (x * b), sq_nonneg (x * c), sq_nonneg (x - 2 * a / (2 * b)), sq_nonneg (x - a / b)]
  linarith