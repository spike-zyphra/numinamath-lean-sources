import Mathlib

open Real

theorem inequalities_241709 :
    IsGreatest {x | ∃ a b c d e f : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ e ≥ 0 ∧ f ≥ 0 ∧ a + b + c + d + e + f = 6 ∧ x = a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b} 8 := by
  constructor
  · -- Show that 8 is achievable
    use 2, 2, 2, 0, 0, 0
    norm_num
  · -- Show that 8 is the greatest value
    intro x hx
    rcases hx with ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, h1, hx⟩
    have h2 : a * b * c + b * c * d + c * d * e + d * e * f + e * f * a + f * a * b ≤ 8 := by
      have h4 : (a + d) * (b + e) * (c + f) ≤ 8 := by
        have h5 : (a + d) + (b + e) + (c + f) = 6 := by
          linarith
        have h6 : (a + d) * (b + e) * (c + f) ≤ (( (a + d) + (b + e) + (c + f) ) / 3) ^ 3 := by
          nlinarith [sq_nonneg ((a + d) - (b + e)), sq_nonneg ((b + e) - (c + f)), sq_nonneg ((a + d) - (c + f)), sq_nonneg ((a + d) + (b + e) + (c + f)), sq_nonneg ((a + d) - (b + e)), sq_nonneg ((b + e) - (c + f)), sq_nonneg ((a + d) - (c + f))]
        rw [h5] at h6
        norm_num at h6 ⊢
        all_goals linarith
      nlinarith [ sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (d - 2), sq_nonneg (e - 2), sq_nonneg (f - 2), 
        sq_nonneg ((a + d) - 2), sq_nonneg ((b + e) - 2), sq_nonneg ((c + f) - 2), 
        mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc hd, mul_nonneg hd he, mul_nonneg he hf, mul_nonneg hf ha, 
        mul_nonneg ha hc, mul_nonneg hb hd, mul_nonneg hc he, mul_nonneg hd hf, mul_nonneg he ha, mul_nonneg hf hb
        ]
    nlinarith [h2, hx]