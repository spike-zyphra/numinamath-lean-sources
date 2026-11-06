import Mathlib

open Real

theorem inequalities_100531 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4)) :
    a + b > c ∧ b + c > a ∧ c + a > b := by

  have h1 : a + b > c := by
    by_contra h2
    push_neg at h2
    have h2' : c ≥ a + b := by linarith
    have h3 : c^2 ≥ (a + b)^2 := by nlinarith [h2']
    have h4 : c^2 ≥ a^2 + b^2 + 2 * a * b := by
      nlinarith [h3]
    have h5 : (a^2 + b^2 + c^2) ^ 2 ≤ 2 * (a^4 + b^4 + c^4) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (c - (a + b)), sq_nonneg (a + b - c), 
          sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          h4
      ]
    nlinarith

  have h2 : b + c > a := by
    by_contra h2
    push_neg at h2
    have h4 : a ≥ b + c := by linarith
    have h5 : a^2 ≥ (b + c)^2 := by nlinarith [h4]
    have h6 : a^2 ≥ b^2 + c^2 + 2 * b * c := by
      nlinarith [h5]
    have h7 : (a^2 + b^2 + c^2) ^ 2 ≤ 2 * (a^4 + b^4 + c^4) := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - (b + c)), sq_nonneg (b + c - a), 
          sq_nonneg (b * c - b * a), sq_nonneg (b * c - c * a), sq_nonneg (b * a - c * a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          h6
      ]
    nlinarith

  have h3 : c + a > b := by
    by_contra h3
    push_neg at h3
    have h5 : b ≥ a + c := by linarith
    have h6 : b^2 ≥ (a + c)^2 := by nlinarith [h5]
    have h7 : b^2 ≥ a^2 + c^2 + 2 * a * c := by
      nlinarith [h6]
    have h8 : (a^2 + b^2 + c^2) ^ 2 ≤ 2 * (a^4 + b^4 + c^4) := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - (a + c)), sq_nonneg (a + c - b), 
          sq_nonneg (a * c - a * b), sq_nonneg (a * c - c * b), sq_nonneg (a * b - c * b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          h7
      ]
    nlinarith
  exact ⟨h1, h2, h3⟩