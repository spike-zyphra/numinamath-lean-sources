import Mathlib

theorem inequalities_604589 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 ≤ (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) ∧
    (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) < 33 / 4 := by
  have h1 : 0 < a + 4 * b := by
    apply add_pos ha
    exact mul_pos (by simp) hb
  have h2 : 0 < b + 4 * c := by
    apply add_pos hb
    exact mul_pos (by simp) hc
  have h3 : 0 < c + 4 * a := by
    apply add_pos hc
    exact mul_pos (by simp) ha
  constructor
  · 
    have h4 : (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) - 3 ≥ 0 := by 
      have h31 : 0 < (a + 4 * b) * (b + 4 * c) * (c + 4 * a) := by positivity
      have h41 : (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) - 3 =
          ((4 * a + b) * (b + 4 * c) * (c + 4 * a) + (4 * b + c) * (a + 4 * b) * (c + 4 * a) + (4 * c + a) * (a + 4 * b) * (b + 4 * c) - 3 * (a + 4 * b) * (b + 4 * c) * (c + 4 * a)) / ((a + 4 * b) * (b + 4 * c) * (c + 4 * a)) := by 
        field_simp
        <;> ring
      rw [h41]
      apply div_nonneg
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)),
                sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)),
                sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)),
                mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
      positivity
    linarith
  · 
    by_contra h
    push_neg at h
    have h5 : (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) ≥ 33 / 4 := by linarith
    have h51 : 0 < (a + 4 * b) * (b + 4 * c) * (c + 4 * a) := by positivity
    have h8 : (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) - 33 / 4 ≥ 0 := by linarith
    have h9 : (4 * a + b) / (a + 4 * b) + (4 * b + c) / (b + 4 * c) + (4 * c + a) / (c + 4 * a) - 33 / 4 =
        ((4 * a + b) * (b + 4 * c) * (c + 4 * a) + (4 * b + c) * (a + 4 * b) * (c + 4 * a) + (4 * c + a) * (a + 4 * b) * (b + 4 * c) - (33 / 4) * (a + 4 * b) * (b + 4 * c) * (c + 4 * a)) / ((a + 4 * b) * (b + 4 * c) * (c + 4 * a)) := by 
      field_simp
      <;> ring
    rw [h9] at h8
    have h10 : ((4 * a + b) * (b + 4 * c) * (c + 4 * a) + (4 * b + c) * (a + 4 * b) * (c + 4 * a) + (4 * c + a) * (a + 4 * b) * (b + 4 * c) - (33 / 4) * (a + 4 * b) * (b + 4 * c) * (c + 4 * a)) ≥ 0 := by
      apply (div_nonneg_iff).mp at h8
      cases h8 with
      | inl h1 => nlinarith
      | inr h2 => nlinarith
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (b - c)), sq_nonneg (a * (c - a)), 
          sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (b * (c - a)), 
          sq_nonneg (c * (a - b)), sq_nonneg (c * (b - c)), sq_nonneg (c * (c - a)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos hc ha, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < c * a by nlinarith), 
          mul_pos (show 0 < c * a by nlinarith) (show 0 < a * b by nlinarith)
]