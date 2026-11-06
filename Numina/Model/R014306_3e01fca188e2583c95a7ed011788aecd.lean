import Mathlib

open Real

theorem inequalities_598125 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ ((a^2 + b^2) / (c^2 + a * b) + (b^2 + c^2) / (a^2 + b * c) +
        (c^2 + a^2) / (b^2 + c * a)) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : 0 < b * c := mul_pos hb hc
  have h3 : 0 < c * a := mul_pos hc ha
  have h4 : a ^ 2 > 0 := sq_pos_of_pos ha
  have h5 : b ^ 2 > 0 := sq_pos_of_pos hb
  have h6 : c ^ 2 > 0 := sq_pos_of_pos hc
  have h7 : c^2 + a * b > 0 := by linarith
  have h8 : a ^ 2 + b * c > 0 := by linarith
  have h9 : b ^ 2 + c * a > 0 := by linarith
  have h10 : ((a^2 + b^2) / (c^2 + a * b) + (b^2 + c^2) / (a^2 + b * c) + (c^2 + a^2) / (b^2 + c * a)) ≥ 3 := by
    have eq1 : (a^2 + b^2) / (c^2 + a * b) + (b^2 + c^2) / (a^2 + b * c) + (c^2 + a^2) / (b^2 + c * a) - 3 ≥ 0 := by
      have eq2 : (a^2 + b^2) / (c^2 + a * b) + (b^2 + c^2) / (a^2 + b * c) + (c^2 + a^2) / (b^2 + c * a) - 3
        = ((a^2 + b^2) * (a^2 + b * c) * (b^2 + c * a) + (b^2 + c^2) * (c^2 + a * b) * (b^2 + c * a) + (c^2 + a^2) * (c^2 + a * b) * (a^2 + b * c) - 3 * (c^2 + a * b) * (a^2 + b * c) * (b^2 + c * a)) / ((c^2 + a * b) * (a^2 + b * c) * (b^2 + c * a)) := by
        field_simp
        ring_nf
        <;> field_simp
        <;> ring
      rw [eq2]
      have h10 : (c^2 + a * b) * (a^2 + b * c) * (b^2 + c * a) > 0 := by positivity
      have h12 : ((a^2 + b^2) * (a^2 + b * c) * (b^2 + c * a) + (b^2 + c^2) * (c^2 + a * b) * (b^2 + c * a) + (c^2 + a^2) * (c^2 + a * b) * (a^2 + b * c) - 3 * (c^2 + a * b) * (a^2 + b * c) * (b^2 + c * a)) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - b)), sq_nonneg ( (a - b) * (a - b) ), sq_nonneg ( (b - c) * (b - c) ), sq_nonneg ( (c - a) * (c - a) ), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, mul_pos (mul_pos ha hb) ha, mul_pos (mul_pos ha hb) hc, mul_pos (mul_pos hb hc) ha, mul_pos (mul_pos hb hc) hc, mul_pos (mul_pos hc ha) hb, mul_pos (mul_pos hc ha) ha]

      apply div_nonneg
      linarith
      all_goals positivity
      all_goals field_simp [h1, h2, h3, h4, h5, h6, h1, h2, h3, mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]
    linarith
  linarith
  all_goals tauto
  all_goals tauto
  all_goals try linarith
  all_goals try nlinarith
  <;> try tauto <;> try nlinarith