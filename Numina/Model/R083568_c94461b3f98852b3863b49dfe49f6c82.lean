import Mathlib

theorem algebra_1472 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
    (hord : a > b ∧ a > c ∧ a > d ∧ d < b ∧ d < c)
    (hprop : a / b = c / d) : a + d > b + c := by

  have h1 : a * d = c * b := by 
    have h2 : b ≠ 0 := by linarith
    have h3 : d ≠ 0 := by linarith
    field_simp [h2, h3] at hprop ⊢
    nlinarith [show 0 < b by linarith, show 0 < d by linarith, hprop, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
  nlinarith [h1, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, 
    show 0 < a * b by nlinarith, show 0 < a * c by nlinarith, show 0 < a * d by nlinarith, show 0 < b * c by nlinarith, show 0 < b * d by nlinarith, show 0 < c * d by nlinarith,
    mul_pos (sub_pos.mpr (show a > b by tauto)) (sub_pos.mpr (show b > d by linarith)), 
    mul_pos (sub_pos.mpr (show a > c by tauto)) (sub_pos.mpr (show c > d by linarith)), 
    hord.1, hord.2.1, hord.2.2.1, hord.2.2.2.1, hord.2.2.2.2
          ]