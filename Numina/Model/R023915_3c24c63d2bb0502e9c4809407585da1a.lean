import Mathlib

theorem inequalities_599646
    (a b c : ℝ)
    (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (hc : 0 ≤ c)
    (hne : ¬(a = 0 ∧ b = 0))
    (hne' : ¬(a = 0 ∧ c = 0))
    (hne'' : ¬(b = 0 ∧ c = 0)) :
    9 / (a + b + c) ^ 2 ≤
    1 / (a ^ 2 + a * b + b ^ 2) +
    1 / (b ^ 2 + b * c + c ^ 2) +
    1 / (c ^ 2 + c * a + a ^ 2) := by 
  have h1 : 0 < a ^ 2 + a * b + b ^ 2 := by
    by_contra h
    push_neg at h
    have h2 : a ^ 2 + a * b + b ^ 2 ≤ 0 := by linarith
    have h3 : a = 0 := by nlinarith
    have h4 : b = 0 := by nlinarith
    have h5 : a = 0 ∧ b = 0 := ⟨h3, h4⟩
    contradiction 
  have h2 : 0 < b ^ 2 + b * c + c ^ 2 := by 
    by_contra h
    push_neg at h
    have h4 : b ^ 2 + b * c + c ^ 2 ≤ 0 := by linarith 
    have h5 : b = 0 := by nlinarith 
    have h6 : c = 0 := by nlinarith 
    have h7 : b = 0 ∧ c = 0 := ⟨h5, h6⟩ 
    contradiction 
  have h3 : 0 < c ^ 2 + c * a + a ^ 2 := by 
    by_contra h 
    push_neg at h 
    have h4 : c ^ 2 + c * a + a ^ 2 ≤ 0 := by linarith 
    have h5 : c = 0 := by nlinarith 
    have h6 : a = 0 := by nlinarith 
    have h7 : a = 0 ∧ c = 0 := ⟨h6, h5⟩ 
    contradiction 
  have h4 : 0 < a + b + c := by 
    by_contra h 
    push_neg at h 
    have h5 : a = 0 := by linarith 
    have h6 : b = 0 := by linarith 
    have h7 : c = 0 := by linarith 
    have h8 : a = 0 ∧ b = 0 := ⟨h5, h6⟩ 
    contradiction 
  have h5 : 1 / (a ^ 2 + a * b + b ^ 2) + 1 / (b ^ 2 + b * c + c ^ 2) + 1 / (c ^ 2 + c * a + a ^ 2) ≥ 9 / (a + b + c) ^ 2 := by 
    have h5 : 0 < (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a + b + c) ^ 2 := by positivity 
    have h6 : (1 / (a ^ 2 + a * b + b ^ 2) + 1 / (b ^ 2 + b * c + c ^ 2) + 1 / (c ^ 2 + c * a + a ^ 2) - 9 / (a + b + c) ^ 2) ≥ 0 := by 
      have h7 : (1 / (a ^ 2 + a * b + b ^ 2) + 1 / (b ^ 2 + b * c + c ^ 2) + 1 / (c ^ 2 + c * a + a ^ 2) - 9 / (a + b + c) ^ 2) = 
        ( (a + b + c) ^ 2 * ( (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ) + 
          (a + b + c) ^ 2 * ( (a ^ 2 + a * b + b ^ 2) * (c ^ 2 + c * a + a ^ 2) ) + 
          (a + b + c) ^ 2 * ( (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) ) - 
          9 * (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) ) / ( (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) * (a + b + c) ^ 2 ) := by 
        field_simp 
        ring 
      rw [h7]
      apply div_nonneg 
      nlinarith [ sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc 
        ]
      positivity 
    linarith 
  linarith